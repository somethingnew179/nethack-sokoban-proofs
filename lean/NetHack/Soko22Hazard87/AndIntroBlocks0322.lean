import NetHack.Soko22Hazard87.AndIntroBlocks0321
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro80500 (p : Pattern) (ha : d307049 p = 1) (hb : d308823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306935 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307008 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d306909 q = 1) (hb : d308808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306909, d308808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80258 q ha hb
    | true =>
      simp only [d306909, d308808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80259 q ha hb
  have h4 (q : Pattern) (ha : d307009 q = 1) (hb : d308809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307009, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307009, d308809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307025 q = 1) (hb : d308810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307025, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307025, d308810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307026 q = 1) (hb : d308811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307026, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307026, d308811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307027 q = 1) (hb : d308812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307027, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307027, d308812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307034 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307039 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d306919 q = 1) (hb : d308818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80261 q ha hb
    | true =>
      simp only [d306919, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80262 q ha hb
  have h13 (q : Pattern) (ha : d307042 q = 1) (hb : d308819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307042, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307046 q = 1) (hb : d308820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307046, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307047 q = 1) (hb : d308821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307047, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307047, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307048 q = 1) (hb : d308822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307048, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307048, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307049 q = 1) (hb : d308823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307049, d308823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307049, d308823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80501 (p : Pattern) (ha : d307069 p = 1) (hb : d309636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307041 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306919 q = 1) (hb : d308818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d306919, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80261 q ha hb
    | true =>
      simp only [d306919, d308818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80262 q ha hb
  have h3 (q : Pattern) (ha : d307042 q = 1) (hb : d308819 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307042, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307042, d308819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307046 q = 1) (hb : d308820 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307046, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307046, d308820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307067 q = 1) (hb : d308821 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307067, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307067, d308821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307068 q = 1) (hb : d308822 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307068, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307068, d308822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307069 q = 1) (hb : d309636 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307069, d309636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307069, d309636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80502 (p : Pattern) (ha : d307190 p = 1) (hb : d309647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307165 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307170 q = 1) (hb : d309642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307170, d309642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80301 q ha hb
    | true =>
      simp only [d307170, d309642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80306 q ha hb
  have h3 (q : Pattern) (ha : d307171 q = 1) (hb : d309643 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307171, d309643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307171, d309643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307186 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307187 q = 1) (hb : d309644 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307187, d309644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307187, d309644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307188 q = 1) (hb : d309645 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307188, d309645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307188, d309645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307189 q = 1) (hb : d309646 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307189, d309646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307189, d309646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307190 q = 1) (hb : d309647 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307190, d309647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307190, d309647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80503 (p : Pattern) (ha : d307203 p = 1) (hb : d309653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d306927 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307050 q = 1) (hb : d308824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307050, d308824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80499 q ha hb
    | true =>
      simp only [d307050, d308824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80500 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307064 q = 1) (hb : d308825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307064, d308825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307064, d308825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307065 q = 1) (hb : d309634 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307065, d309634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307065, d309634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307066 q = 1) (hb : d309635 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307066, d309635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307066, d309635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307070 q = 1) (hb : d309637 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307070, d309637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307070, d309637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80501 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307073 q = 1) (hb : d309638 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307073, d309638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307073, d309638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307074 q = 1) (hb : d309639 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307074, d309639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307074, d309639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307075 q = 1) (hb : d309640 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307075, d309640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307075, d309640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307076 q = 1) (hb : d309641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307076, d309641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307076, d309641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307191 q = 1) (hb : d309648 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307191, d309648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307191, d309648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80502 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307199 q = 1) (hb : d309649 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307199, d309649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307199, d309649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307200 q = 1) (hb : d309650 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307200, d309650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307200, d309650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307201 q = 1) (hb : d309651 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307201, d309651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307201, d309651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307202 q = 1) (hb : d309652 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307202, d309652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307202, d309652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307203 q = 1) (hb : d309653 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307203, d309653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307203, d309653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80504 (p : Pattern) (ha : d307209 p = 1) (hb : d309659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307204 q = 1) (hb : d309654 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307204, d309654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307204, d309654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80503 q ha hb
  have h2 (q : Pattern) (ha : d307205 q = 1) (hb : d309655 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307205, d309655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307205, d309655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307206 q = 1) (hb : d309656 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307206, d309656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307206, d309656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307207 q = 1) (hb : d309657 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307207, d309657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307207, d309657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307208 q = 1) (hb : d309658 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307208, d309658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307208, d309658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307209 q = 1) (hb : d309659 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307209, d309659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307209, d309659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80505 (p : Pattern) (ha : d307443 p = 1) (hb : d309183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d307324 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80325 q ha hb
    | true =>
      simp only [d307324, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80326 q ha hb
  have h5 (q : Pattern) (ha : d307411 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307411, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d307440 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307440, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d307441 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307441, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307442 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307442, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307443 q = 1) (hb : d309183 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307443, d309183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307443, d309183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80506 (p : Pattern) (ha : d307464 p = 1) (hb : d309193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307350 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307410 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307324 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307324, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80325 q ha hb
    | true =>
      simp only [d307324, d309178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80326 q ha hb
  have h4 (q : Pattern) (ha : d307411 q = 1) (hb : d309179 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307411, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d307411, d309179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d307440 q = 1) (hb : d309180 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307440, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307440, d309180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d307441 q = 1) (hb : d309181 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307441, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307441, d309181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307442 q = 1) (hb : d309182 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307442, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307442, d309182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307449 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307454 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d307334 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80328 q ha hb
    | true =>
      simp only [d307334, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80329 q ha hb
  have h13 (q : Pattern) (ha : d307457 q = 1) (hb : d309189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d307457, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307461 q = 1) (hb : d309190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307461, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307462 q = 1) (hb : d309191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307462, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d307462, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d307463 q = 1) (hb : d309192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307463, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d307463, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d307464 q = 1) (hb : d309193 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307464, d309193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d307464, d309193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80507 (p : Pattern) (ha : d307484 p = 1) (hb : d309665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307456 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307334 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307334, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80328 q ha hb
    | true =>
      simp only [d307334, d309188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80329 q ha hb
  have h3 (q : Pattern) (ha : d307457 q = 1) (hb : d309189 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307457, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307457, d309189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307460 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307461 q = 1) (hb : d309190 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307461, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307461, d309190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307482 q = 1) (hb : d309191 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307482, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307482, d309191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307483 q = 1) (hb : d309192 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307483, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307483, d309192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307484 q = 1) (hb : d309665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307484, d309665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307484, d309665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80508 (p : Pattern) (ha : d307616 p = 1) (hb : d309676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307585 q = 1) (hb : d309671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307585, d309671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80369 q ha hb
    | true =>
      simp only [d307585, d309671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80375 q ha hb
  have h3 (q : Pattern) (ha : d307586 q = 1) (hb : d309672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307586, d309672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307586, d309672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307613 q = 1) (hb : d309673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307613, d309673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307613, d309673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307614 q = 1) (hb : d309674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307614, d309674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307614, d309674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307615 q = 1) (hb : d309675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307615, d309675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307615, d309675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307616 q = 1) (hb : d309676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307616, d309676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307616, d309676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80509 (p : Pattern) (ha : d307629 p = 1) (hb : d309682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307465 q = 1) (hb : d309194 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307465, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80505 q ha hb
    | true =>
      simp only [d307465, d309194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80506 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d307479 q = 1) (hb : d309195 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307479, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307479, d309195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307480 q = 1) (hb : d309663 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307480, d309663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307480, d309663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307481 q = 1) (hb : d309664 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307481, d309664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307481, d309664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307485 q = 1) (hb : d309666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307485, d309666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307485, d309666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80507 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307487 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307488 q = 1) (hb : d309667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307488, d309667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307488, d309667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307489 q = 1) (hb : d309668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307489, d309668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307489, d309668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307490 q = 1) (hb : d309669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307490, d309669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307490, d309669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307491 q = 1) (hb : d309670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307491, d309670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307491, d309670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307617 q = 1) (hb : d309677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307617, d309677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307617, d309677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80508 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307625 q = 1) (hb : d309678 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307625, d309678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307625, d309678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307626 q = 1) (hb : d309679 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307626, d309679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307626, d309679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307627 q = 1) (hb : d309680 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307627, d309680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307627, d309680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307628 q = 1) (hb : d309681 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307628, d309681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307628, d309681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307629 q = 1) (hb : d309682 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307629, d309682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307629, d309682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80510 (p : Pattern) (ha : d307635 p = 1) (hb : d309688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307630 q = 1) (hb : d309683 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307630, d309683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307630, d309683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80509 q ha hb
  have h2 (q : Pattern) (ha : d307631 q = 1) (hb : d309684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307631, d309684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307631, d309684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307632 q = 1) (hb : d309685 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307632, d309685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307632, d309685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307633 q = 1) (hb : d309686 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307633, d309686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307633, d309686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307634 q = 1) (hb : d309687 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307634, d309687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307634, d309687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307635 q = 1) (hb : d309688 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307635, d309688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307635, d309688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80511 (p : Pattern) (ha : d44504 p = 1) (hb : d307774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307733 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307747 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44499 q = 1) (hb : d307698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d307698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80388 q ha hb
    | true =>
      simp only [d44499, d307698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80389 q ha hb
  have h5 (q : Pattern) (ha : d44500 q = 1) (hb : d307748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d307748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44500, d307748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d307770 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44501 q = 1) (hb : d307771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d307771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44501, d307771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44502 q = 1) (hb : d307772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d307772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44502, d307772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44503 q = 1) (hb : d307773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d307773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44503, d307773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44504 q = 1) (hb : d307774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d307774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d307774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80512 (p : Pattern) (ha : d44514 p = 1) (hb : d307795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307733 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44499 q = 1) (hb : d307698 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d307698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80388 q ha hb
    | true =>
      simp only [d44499, d307698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80389 q ha hb
  have h4 (q : Pattern) (ha : d44500 q = 1) (hb : d307748 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d307748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44500, d307748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d307770 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44501 q = 1) (hb : d307771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d307771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44501, d307771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44502 q = 1) (hb : d307772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d307772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44502, d307772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44503 q = 1) (hb : d307773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d307773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d307773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d307780 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d307785 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d307787 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d44509 q = 1) (hb : d307708 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d307708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80391 q ha hb
    | true =>
      simp only [d44509, d307708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80392 q ha hb
  have h13 (q : Pattern) (ha : d44510 q = 1) (hb : d307788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d307788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44510, d307788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307791 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44511 q = 1) (hb : d307792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d307792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44511, d307792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44512 q = 1) (hb : d307793 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d307793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44512, d307793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44513 q = 1) (hb : d307794 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d307794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44513, d307794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44514 q = 1) (hb : d307795 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d307795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44514, d307795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80513 (p : Pattern) (ha : d307815 p = 1) (hb : d309695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307787 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d44509 q = 1) (hb : d307708 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d307708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80391 q ha hb
    | true =>
      simp only [d44509, d307708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80392 q ha hb
  have h3 (q : Pattern) (ha : d44510 q = 1) (hb : d307788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d307788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44510, d307788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307791 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44511 q = 1) (hb : d307792 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d307792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44511, d307792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44512 q = 1) (hb : d307813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d307813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d307813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44513 q = 1) (hb : d307814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d307814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d307814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307815 q = 1) (hb : d309695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307815, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307815, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro80514 (p : Pattern) (ha : d307906 p = 1) (hb : d309706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d307875 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d307880 q = 1) (hb : d309701 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d307880, d309701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80428 q hb ha
    | true =>
      simp only [d307880, d309701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80400 q hb ha
  have h3 (q : Pattern) (ha : d307881 q = 1) (hb : d309702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d307881, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307881, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307903 q = 1) (hb : d309703 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d307903, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307903, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307904 q = 1) (hb : d309704 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d307904, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307904, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307905 q = 1) (hb : d309705 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d307905, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307905, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d307906 q = 1) (hb : d309706 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d307906, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307906, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80515 (p : Pattern) (ha : d307919 p = 1) (hb : d309712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d307716 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d307796 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d307796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80511 q ha hb
    | true =>
      simp only [d44515, d307796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80512 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d307809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44516 q = 1) (hb : d307810 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d307810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d307810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d307811 q = 1) (hb : d309693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307811, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d307811, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d307812 q = 1) (hb : d309694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307812, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307812, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307816 q = 1) (hb : d309696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307816, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307816, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80513 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d307818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d307819 q = 1) (hb : d309697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307819, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d307819, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d307820 q = 1) (hb : d309698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307820, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d307820, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d307821 q = 1) (hb : d309699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307821, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307821, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d307822 q = 1) (hb : d309700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307822, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307822, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307907 q = 1) (hb : d309707 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d307907, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d307907, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80514 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d307914 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d307915 q = 1) (hb : d309708 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d307915, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d307915, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d307916 q = 1) (hb : d309709 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d307916, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307916, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d307917 q = 1) (hb : d309710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d307917, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d307917, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d307918 q = 1) (hb : d309711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d307918, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d307918, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d307919 q = 1) (hb : d309712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d307919, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d307919, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80516 (p : Pattern) (ha : d307925 p = 1) (hb : d309718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307920 q = 1) (hb : d309713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d307920, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307920, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80515 q ha hb
  have h2 (q : Pattern) (ha : d307921 q = 1) (hb : d309714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d307921, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307921, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d307922 q = 1) (hb : d309715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d307922, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307922, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307923 q = 1) (hb : d309716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d307923, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307923, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d307924 q = 1) (hb : d309717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d307924, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307924, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307925 q = 1) (hb : d309718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d307925, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d307925, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80517 (p : Pattern) (ha : d307931 p = 1) (hb : d309724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d306523 q = 1) (hb : d309605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306523, d309605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80486 q ha hb
    | true =>
      simp only [d306523, d309605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80492 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d306816 q = 1) (hb : d309632 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d306816, d309632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d306816, d309632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80498 q ha hb
  have h3 (q : Pattern) (ha : d306817 q = 1) (hb : d309633 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d306817, d309633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d306817, d309633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d307210 q = 1) (hb : d309660 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307210, d309660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307210, d309660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80504 q ha hb
  have h5 (q : Pattern) (ha : d307211 q = 1) (hb : d309661 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307211, d309661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307211, d309661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d307212 q = 1) (hb : d309662 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307212, d309662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307212, d309662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d307636 q = 1) (hb : d309689 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307636, d309689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307636, d309689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80510 q ha hb
  have h8 (q : Pattern) (ha : d307637 q = 1) (hb : d309690 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307637, d309690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307637, d309690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d307638 q = 1) (hb : d309691 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307638, d309691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307638, d309691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d307639 q = 1) (hb : d309692 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307639, d309692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d307639, d309692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d307926 q = 1) (hb : d309719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d307926, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307926, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80516 q ha hb
  have h12 (q : Pattern) (ha : d307927 q = 1) (hb : d309720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d307927, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307927, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d307928 q = 1) (hb : d309721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d307928, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307928, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d307929 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d307929, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d307929, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d307930 q = 1) (hb : d309723 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d307930, d309723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d307930, d309723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d307931 q = 1) (hb : d309724 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d307931, d309724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d307931, d309724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro80518 (p : Pattern) (ha : d307937 p = 1) (hb : d309730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307932 q = 1) (hb : d309725 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d307932, d309725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80517 q ha hb
    | true =>
      simp only [d307932, d309725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307933 q = 1) (hb : d309726 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d307933, d309726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307933, d309726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307934 q = 1) (hb : d309727 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d307934, d309727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307934, d309727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307935 q = 1) (hb : d309728 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d307935, d309728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307935, d309728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307936 q = 1) (hb : d309729 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d307936, d309729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307936, d309729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307937 q = 1) (hb : d309730 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d307937, d309730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307937, d309730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro80519 (p : Pattern) (ha : d307943 p = 1) (hb : d309736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307938 q = 1) (hb : d309731 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d307938, d309731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80518 q ha hb
    | true =>
      simp only [d307938, d309731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307939 q = 1) (hb : d309732 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d307939, d309732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307939, d309732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307940 q = 1) (hb : d309733 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d307940, d309733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307940, d309733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307941 q = 1) (hb : d309734 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d307941, d309734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307941, d309734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307942 q = 1) (hb : d309735 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d307942, d309735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307942, d309735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307943 q = 1) (hb : d309736 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d307943, d309736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307943, d309736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro80520 (p : Pattern) (ha : d307949 p = 1) (hb : d309742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307944 q = 1) (hb : d309737 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d307944, d309737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80519 q ha hb
    | true =>
      simp only [d307944, d309737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307945 q = 1) (hb : d309738 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d307945, d309738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307945, d309738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307946 q = 1) (hb : d309739 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d307946, d309739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307946, d309739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307947 q = 1) (hb : d309740 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d307947, d309740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307947, d309740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307948 q = 1) (hb : d309741 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d307948, d309741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307948, d309741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307949 q = 1) (hb : d309742 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d307949, d309742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307949, d309742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro80521 (p : Pattern) (ha : d307955 p = 1) (hb : d309748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307950 q = 1) (hb : d309743 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d307950, d309743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80520 q ha hb
    | true =>
      simp only [d307950, d309743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307951 q = 1) (hb : d309744 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d307951, d309744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307951, d309744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307952 q = 1) (hb : d309745 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d307952, d309745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307952, d309745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307953 q = 1) (hb : d309746 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d307953, d309746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307953, d309746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307954 q = 1) (hb : d309747 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d307954, d309747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307954, d309747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307955 q = 1) (hb : d309748 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d307955, d309748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307955, d309748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro80522 (p : Pattern) (ha : d307961 p = 1) (hb : d309754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307956 q = 1) (hb : d309749 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d307956, d309749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80521 q ha hb
    | true =>
      simp only [d307956, d309749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307957 q = 1) (hb : d309750 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d307957, d309750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307957, d309750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307958 q = 1) (hb : d309751 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d307958, d309751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307958, d309751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307959 q = 1) (hb : d309752 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d307959, d309752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307959, d309752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307960 q = 1) (hb : d309753 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d307960, d309753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307960, d309753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307961 q = 1) (hb : d309754 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d307961, d309754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307961, d309754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro80523 (p : Pattern) (ha : d307967 p = 1) (hb : d309760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307962 q = 1) (hb : d309755 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d307962, d309755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80522 q ha hb
    | true =>
      simp only [d307962, d309755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307963 q = 1) (hb : d309756 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d307963, d309756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307963, d309756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307964 q = 1) (hb : d309757 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d307964, d309757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307964, d309757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307965 q = 1) (hb : d309758 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d307965, d309758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307965, d309758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307966 q = 1) (hb : d309759 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d307966, d309759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307966, d309759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307967 q = 1) (hb : d309760 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d307967, d309760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307967, d309760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro80524 (p : Pattern) (ha : d307973 p = 1) (hb : d309766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d307968 q = 1) (hb : d309761 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d307968, d309761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80523 q ha hb
    | true =>
      simp only [d307968, d309761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d307969 q = 1) (hb : d309762 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d307969, d309762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d307969, d309762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d307970 q = 1) (hb : d309763 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d307970, d309763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d307970, d309763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d307971 q = 1) (hb : d309764 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d307971, d309764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d307971, d309764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d307972 q = 1) (hb : d309765 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d307972, d309765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d307972, d309765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d307973 q = 1) (hb : d309766 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d307973, d309766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d307973, d309766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro80525 (p : Pattern) (ha : d44504 p = 1) (hb : d309471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44525 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44534 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44548 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44500 q = 1) (hb : d309467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44500, d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44630 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44501 q = 1) (hb : d309468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44501, d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44502 q = 1) (hb : d309469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44502, d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44503 q = 1) (hb : d309470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44503, d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44504 q = 1) (hb : d309471 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d309471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d309471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80526 (p : Pattern) (ha : d44514 p = 1) (hb : d309476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44525 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44534 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44548 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44499 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d44500 q = 1) (hb : d309467 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44500, d309467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44630 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d44501 q = 1) (hb : d309468 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44501, d309468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44502 q = 1) (hb : d309469 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44502, d309469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44503 q = 1) (hb : d309470 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d309470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d44640 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d44645 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44647 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d44510 q = 1) (hb : d309472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44510, d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44654 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d44511 q = 1) (hb : d309473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44511, d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d44512 q = 1) (hb : d309474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d309474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44512, d309474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44513 q = 1) (hb : d309475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d309475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44513, d309475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d44514 q = 1) (hb : d309476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d309476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44514, d309476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80527 (p : Pattern) (ha : d309483 p = 1) (hb : d309695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44647 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44510 q = 1) (hb : d309472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44510, d309472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44654 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d44511 q = 1) (hb : d309473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44511, d309473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44512 q = 1) (hb : d309481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d309481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d309481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44513 q = 1) (hb : d309482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d309482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d309482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309483 q = 1) (hb : d309695 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309483, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309483, d309695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro80528 (p : Pattern) (ha : d309493 p = 1) (hb : d309706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44738 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309701 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309489 q = 1) (hb : d309702 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309489, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309489, d309702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44804 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309490 q = 1) (hb : d309703 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309490, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309490, d309703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d309491 q = 1) (hb : d309704 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309491, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309491, d309704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309492 q = 1) (hb : d309705 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309492, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309492, d309705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309493 q = 1) (hb : d309706 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309493, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309493, d309706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80529 (p : Pattern) (ha : d309499 p = 1) (hb : d309712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d44517 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44515 q = 1) (hb : d309477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d309477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80525 q ha hb
    | true =>
      simp only [d44515, d309477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80526 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44672 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d44516 q = 1) (hb : d309478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d309478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44516, d309478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309479 q = 1) (hb : d309693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309479, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309479, d309693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309480 q = 1) (hb : d309694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309480, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309480, d309694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309484 q = 1) (hb : d309696 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309484, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309484, d309696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80527 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d44681 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309485 q = 1) (hb : d309697 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309485, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309485, d309697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d309486 q = 1) (hb : d309698 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309486, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309486, d309698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309487 q = 1) (hb : d309699 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309487, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309487, d309699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309488 q = 1) (hb : d309700 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309488, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309488, d309700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309494 q = 1) (hb : d309707 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309494, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309494, d309707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80528 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44820 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309495 q = 1) (hb : d309708 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309495, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309495, d309708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309496 q = 1) (hb : d309709 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309496, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309496, d309709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309497 q = 1) (hb : d309710 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309497, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309497, d309710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309498 q = 1) (hb : d309711 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309498, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309498, d309711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309499 q = 1) (hb : d309712 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309499, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309499, d309712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80530 (p : Pattern) (ha : d309505 p = 1) (hb : d309718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309500 q = 1) (hb : d309713 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309500, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309500, d309713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80529 q ha hb
  have h2 (q : Pattern) (ha : d309501 q = 1) (hb : d309714 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309501, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309501, d309714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309502 q = 1) (hb : d309715 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309502, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309502, d309715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309503 q = 1) (hb : d309716 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309503, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309503, d309716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309504 q = 1) (hb : d309717 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309504, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309504, d309717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309505 q = 1) (hb : d309718 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309505, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309505, d309718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80531 (p : Pattern) (ha : d104 p = 1) (hb : d309771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42274 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100 q = 1) (hb : d309767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d309767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d100, d309767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d101 q = 1) (hb : d309768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d309768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101, d309768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102 q = 1) (hb : d309769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d309769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102, d309769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d103 q = 1) (hb : d309770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d309770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d103, d309770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d104 q = 1) (hb : d309771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, d309771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, d309771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80532 (p : Pattern) (ha : d111 p = 1) (hb : d309776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d100 q = 1) (hb : d309767 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d309767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d100, d309767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d101 q = 1) (hb : d309768 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d309768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101, d309768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d102 q = 1) (hb : d309769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d309769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102, d309769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d103 q = 1) (hb : d309770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d309770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d309770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d198 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42281 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d107 q = 1) (hb : d309772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d309772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107, d309772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d108 q = 1) (hb : d309773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d309773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108, d309773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109 q = 1) (hb : d309774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d309774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109, d309774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d110 q = 1) (hb : d309775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d309775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d110, d309775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d111 q = 1) (hb : d309776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, d309776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d111, d309776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80533 (p : Pattern) (ha : d406 p = 1) (hb : d309783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42281 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d309772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d309772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d309772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d309773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d309773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d309773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d309781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, d309781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, d309781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d309782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, d309782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, d309782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d309783 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, d309783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, d309783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80534 (p : Pattern) (ha : d462 p = 1) (hb : d309793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42317 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d309789 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d309789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d309789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d309790 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d309790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d309790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d309791 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, d309791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, d309791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d309792 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, d309792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, d309792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d309793 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, d309793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, d309793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80535 (p : Pattern) (ha : d53647 p = 1) (hb : d309799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d114 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d309777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d309777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80531 q ha hb
    | true =>
      simp only [d112, d309777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80532 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113 q = 1) (hb : d309778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d309778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, d309778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53637 q = 1) (hb : d309779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, d309779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53637, d309779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53638 q = 1) (hb : d309780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, d309780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, d309780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d407 q = 1) (hb : d309784 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d309784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d407, d309784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80533 q ha hb
  have h8 (q : Pattern) (ha : d53639 q = 1) (hb : d309785 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, d309785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53639, d309785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d53640 q = 1) (hb : d309786 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, d309786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53640, d309786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d53641 q = 1) (hb : d309787 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, d309787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53641, d309787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d53642 q = 1) (hb : d309788 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, d309788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53642, d309788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d463 q = 1) (hb : d309794 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d309794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d463, d309794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80534 q ha hb
  have h13 (q : Pattern) (ha : d53643 q = 1) (hb : d309795 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, d309795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53643, d309795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d53644 q = 1) (hb : d309796 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, d309796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53644, d309796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d53645 q = 1) (hb : d309797 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, d309797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d53645, d309797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d53646 q = 1) (hb : d309798 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, d309798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53646, d309798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d53647 q = 1) (hb : d309799 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, d309799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53647, d309799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro80536 (p : Pattern) (ha : d308063 p = 1) (hb : d309809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d307999 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d308059 q = 1) (hb : d309805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308059, d309805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d308059, d309805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d308060 q = 1) (hb : d309806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308060, d309806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d308060, d309806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308061 q = 1) (hb : d309807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308061, d309807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308061, d309807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308062 q = 1) (hb : d309808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308062, d309808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308062, d309808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308063 q = 1) (hb : d309809 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d308063, d309809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308063, d309809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80537 (p : Pattern) (ha : d308070 p = 1) (hb : d309814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42354 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d307999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308059 q = 1) (hb : d309805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308059, d309805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308059, d309805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42432 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d308060 q = 1) (hb : d309806 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308060, d309806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d308060, d309806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308061 q = 1) (hb : d309807 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308061, d309807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308061, d309807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308062 q = 1) (hb : d309808 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308062, d309808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308062, d309808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42441 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42445 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d308006 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d308066 q = 1) (hb : d309810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308066, d309810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d308066, d309810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d308067 q = 1) (hb : d309811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308067, d309811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d308067, d309811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308068 q = 1) (hb : d309812 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308068, d309812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d308068, d309812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308069 q = 1) (hb : d309813 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308069, d309813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d308069, d309813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d308070 q = 1) (hb : d309814 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d308070, d309814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d308070, d309814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80538 (p : Pattern) (ha : d309556 p = 1) (hb : d309821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42447 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308006 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308066 q = 1) (hb : d309810 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308066, d309810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308066, d309810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42453 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d308067 q = 1) (hb : d309811 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308067, d309811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d308067, d309811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308068 q = 1) (hb : d309819 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308068, d309819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308068, d309819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308069 q = 1) (hb : d309820 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308069, d309820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308069, d309820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309556 q = 1) (hb : d309821 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309556, d309821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309556, d309821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80539 (p : Pattern) (ha : d309566 p = 1) (hb : d309831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308042 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309562 q = 1) (hb : d309827 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309562, d309827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309562, d309827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42521 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309563 q = 1) (hb : d309828 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309563, d309828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309563, d309828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309564 q = 1) (hb : d309829 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309564, d309829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309564, d309829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309565 q = 1) (hb : d309830 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309565, d309830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309565, d309830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309566 q = 1) (hb : d309831 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309566, d309831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309566, d309831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80540 (p : Pattern) (ha : d309572 p = 1) (hb : d309837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308071 q = 1) (hb : d309815 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d308071, d309815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80536 q ha hb
    | true =>
      simp only [d308071, d309815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80537 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42460 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308072 q = 1) (hb : d309816 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d308072, d309816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308072, d309816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309554 q = 1) (hb : d309817 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309554, d309817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309554, d309817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309555 q = 1) (hb : d309818 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309555, d309818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309555, d309818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309557 q = 1) (hb : d309822 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309557, d309822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309557, d309822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80538 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309558 q = 1) (hb : d309823 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309558, d309823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309558, d309823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309559 q = 1) (hb : d309824 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309559, d309824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309559, d309824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309560 q = 1) (hb : d309825 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309560, d309825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309560, d309825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309561 q = 1) (hb : d309826 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309561, d309826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309561, d309826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309567 q = 1) (hb : d309832 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309567, d309832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309567, d309832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80539 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309568 q = 1) (hb : d309833 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309568, d309833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309568, d309833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309569 q = 1) (hb : d309834 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309569, d309834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309569, d309834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309570 q = 1) (hb : d309835 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309570, d309835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309570, d309835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309571 q = 1) (hb : d309836 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309571, d309836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309571, d309836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309572 q = 1) (hb : d309837 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309572, d309837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309572, d309837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80541 (p : Pattern) (ha : d309578 p = 1) (hb : d309843 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d309573 q = 1) (hb : d309838 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309573, d309838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309573, d309838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80540 q ha hb
  have h8 (q : Pattern) (ha : d309574 q = 1) (hb : d309839 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309574, d309839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309574, d309839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309575 q = 1) (hb : d309840 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309575, d309840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309575, d309840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309576 q = 1) (hb : d309841 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309576, d309841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309576, d309841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309577 q = 1) (hb : d309842 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309577, d309842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309577, d309842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d309578 q = 1) (hb : d309843 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309578, d309843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309578, d309843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80542 (p : Pattern) (ha : d308233 p = 1) (hb : d309848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d308228 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d308229 q = 1) (hb : d309844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308229, d309844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d308229, d309844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d308230 q = 1) (hb : d309845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308230, d309845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d308230, d309845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308231 q = 1) (hb : d309846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308231, d309846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308231, d309846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308232 q = 1) (hb : d309847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308232, d309847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308232, d309847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308233 q = 1) (hb : d309848 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d308233, d309848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308233, d309848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80543 (p : Pattern) (ha : d308243 p = 1) (hb : d309853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42581 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308228 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308229 q = 1) (hb : d309844 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308229, d309844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308229, d309844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d42695 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d308230 q = 1) (hb : d309845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308230, d309845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d308230, d309845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308231 q = 1) (hb : d309846 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308231, d309846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308231, d309846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308232 q = 1) (hb : d309847 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308232, d309847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308232, d309847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42705 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d42710 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d308238 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d308239 q = 1) (hb : d309849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308239, d309849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d308239, d309849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d308240 q = 1) (hb : d309850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308240, d309850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d308240, d309850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308241 q = 1) (hb : d309851 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308241, d309851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d308241, d309851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308242 q = 1) (hb : d309852 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308242, d309852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d308242, d309852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d308243 q = 1) (hb : d309853 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d308243, d309853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d308243, d309853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80544 (p : Pattern) (ha : d309581 p = 1) (hb : d309860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42712 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308238 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308239 q = 1) (hb : d309849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308239, d309849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308239, d309849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42719 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d308240 q = 1) (hb : d309850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308240, d309850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d308240, d309850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308241 q = 1) (hb : d309858 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308241, d309858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308241, d309858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308242 q = 1) (hb : d309859 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308242, d309859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308242, d309859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309581 q = 1) (hb : d309860 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309581, d309860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309581, d309860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80545 (p : Pattern) (ha : d309592 p = 1) (hb : d309870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42795 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309588 q = 1) (hb : d309866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309588, d309866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309588, d309866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42835 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309589 q = 1) (hb : d309867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309589, d309867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309589, d309867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309590 q = 1) (hb : d309868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309590, d309868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309590, d309868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309591 q = 1) (hb : d309869 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309591, d309869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309591, d309869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309592 q = 1) (hb : d309870 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309592, d309870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309592, d309870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80546 (p : Pattern) (ha : d309598 p = 1) (hb : d309876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308244 q = 1) (hb : d309854 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d308244, d309854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80542 q ha hb
    | true =>
      simp only [d308244, d309854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80543 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42737 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308245 q = 1) (hb : d309855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d308245, d309855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308245, d309855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309579 q = 1) (hb : d309856 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309579, d309856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309579, d309856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309580 q = 1) (hb : d309857 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309580, d309857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309580, d309857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309582 q = 1) (hb : d309861 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309582, d309861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309582, d309861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80544 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d42746 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309583 q = 1) (hb : d309862 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309583, d309862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309583, d309862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309584 q = 1) (hb : d309863 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309584, d309863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309584, d309863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309585 q = 1) (hb : d309864 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309585, d309864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309585, d309864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309586 q = 1) (hb : d309865 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309586, d309865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309586, d309865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309593 q = 1) (hb : d309871 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309593, d309871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309593, d309871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80545 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d42851 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309594 q = 1) (hb : d309872 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309594, d309872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309594, d309872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309595 q = 1) (hb : d309873 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309595, d309873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309595, d309873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309596 q = 1) (hb : d309874 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309596, d309874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309596, d309874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309597 q = 1) (hb : d309875 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309597, d309875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309597, d309875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309598 q = 1) (hb : d309876 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309598, d309876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309598, d309876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80547 (p : Pattern) (ha : d309604 p = 1) (hb : d309882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309599 q = 1) (hb : d309877 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309599, d309877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309599, d309877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80546 q ha hb
  have h2 (q : Pattern) (ha : d309600 q = 1) (hb : d309878 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309600, d309878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309600, d309878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309601 q = 1) (hb : d309879 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309601, d309879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309601, d309879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309602 q = 1) (hb : d309880 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309602, d309880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309602, d309880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309603 q = 1) (hb : d309881 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309603, d309881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309603, d309881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309604 q = 1) (hb : d309882 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309604, d309882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309604, d309882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80548 (p : Pattern) (ha : d308491 p = 1) (hb : d309888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d308486 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d308487 q = 1) (hb : d309884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308487, d309884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d308487, d309884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d308488 q = 1) (hb : d309885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308488, d309885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d308488, d309885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308489 q = 1) (hb : d309886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308489, d309886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308489, d309886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308490 q = 1) (hb : d309887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308490, d309887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308490, d309887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308491 q = 1) (hb : d309888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d308491, d309888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308491, d309888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80549 (p : Pattern) (ha : d308501 p = 1) (hb : d309893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42999 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308486 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308487 q = 1) (hb : d309884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308487, d309884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308487, d309884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d308488 q = 1) (hb : d309885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308488, d309885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d308488, d309885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308489 q = 1) (hb : d309886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308489, d309886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308489, d309886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308490 q = 1) (hb : d309887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308490, d309887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308490, d309887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43086 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43091 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d308496 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d308497 q = 1) (hb : d309889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308497, d309889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d308497, d309889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d308498 q = 1) (hb : d309890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308498, d309890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d308498, d309890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308499 q = 1) (hb : d309891 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308499, d309891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d308499, d309891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308500 q = 1) (hb : d309892 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308500, d309892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d308500, d309892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d308501 q = 1) (hb : d309893 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d308501, d309893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d308501, d309893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80550 (p : Pattern) (ha : d309608 p = 1) (hb : d309900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43093 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308496 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308497 q = 1) (hb : d309889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308497, d309889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308497, d309889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43100 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d308498 q = 1) (hb : d309890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308498, d309890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d308498, d309890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308499 q = 1) (hb : d309898 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308499, d309898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308499, d309898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308500 q = 1) (hb : d309899 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308500, d309899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308500, d309899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309608 q = 1) (hb : d309900 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309608, d309900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309608, d309900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80551 (p : Pattern) (ha : d309619 p = 1) (hb : d309910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309615 q = 1) (hb : d309906 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309615, d309906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309615, d309906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43248 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309616 q = 1) (hb : d309907 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309616, d309907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309616, d309907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309617 q = 1) (hb : d309908 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309617, d309908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309617, d309908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309618 q = 1) (hb : d309909 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309618, d309909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309618, d309909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309619 q = 1) (hb : d309910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309619, d309910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309619, d309910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80552 (p : Pattern) (ha : d309625 p = 1) (hb : d309916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d42917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308502 q = 1) (hb : d309894 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d308502, d309894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80548 q ha hb
    | true =>
      simp only [d308502, d309894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80549 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43118 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308503 q = 1) (hb : d309895 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d308503, d309895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308503, d309895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309606 q = 1) (hb : d309896 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309606, d309896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309606, d309896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309607 q = 1) (hb : d309897 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309607, d309897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309607, d309897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309609 q = 1) (hb : d309901 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309609, d309901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309609, d309901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80550 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43127 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309610 q = 1) (hb : d309902 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309610, d309902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309610, d309902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309611 q = 1) (hb : d309903 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309611, d309903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309611, d309903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309612 q = 1) (hb : d309904 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309612, d309904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309612, d309904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309613 q = 1) (hb : d309905 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309613, d309905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309613, d309905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309620 q = 1) (hb : d309911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309620, d309911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309620, d309911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80551 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43264 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309621 q = 1) (hb : d309912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309621, d309912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309621, d309912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309622 q = 1) (hb : d309913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309622, d309913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309622, d309913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309623 q = 1) (hb : d309914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309623, d309914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309623, d309914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309624 q = 1) (hb : d309915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309624, d309915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309624, d309915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309625 q = 1) (hb : d309916 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309625, d309916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309625, d309916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80553 (p : Pattern) (ha : d309631 p = 1) (hb : d309922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309626 q = 1) (hb : d309917 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309626, d309917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309626, d309917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80552 q ha hb
  have h2 (q : Pattern) (ha : d309627 q = 1) (hb : d309918 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309627, d309918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309627, d309918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309628 q = 1) (hb : d309919 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309628, d309919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309628, d309919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309629 q = 1) (hb : d309920 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309629, d309920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309629, d309920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309630 q = 1) (hb : d309921 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309630, d309921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309630, d309921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309631 q = 1) (hb : d309922 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309631, d309922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309631, d309922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80554 (p : Pattern) (ha : d308813 p = 1) (hb : d309929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d308808 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d308809 q = 1) (hb : d309925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308809, d309925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d308809, d309925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d308810 q = 1) (hb : d309926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308810, d309926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d308810, d309926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308811 q = 1) (hb : d309927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308811, d309927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308811, d309927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308812 q = 1) (hb : d309928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308812, d309928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308812, d309928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308813 q = 1) (hb : d309929 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d308813, d309929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308813, d309929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80555 (p : Pattern) (ha : d308823 p = 1) (hb : d309934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43404 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43468 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308808 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308809 q = 1) (hb : d309925 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308809, d309925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d308809, d309925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d43595 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d308810 q = 1) (hb : d309926 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308810, d309926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d308810, d309926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308811 q = 1) (hb : d309927 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308811, d309927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308811, d309927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308812 q = 1) (hb : d309928 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308812, d309928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308812, d309928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d43605 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d43610 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d308818 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d308819 q = 1) (hb : d309930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308819, d309930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d308819, d309930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d308820 q = 1) (hb : d309931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308820, d309931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d308820, d309931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308821 q = 1) (hb : d309932 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308821, d309932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d308821, d309932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308822 q = 1) (hb : d309933 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308822, d309933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d308822, d309933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d308823 q = 1) (hb : d309934 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d308823, d309934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d308823, d309934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80556 (p : Pattern) (ha : d309636 p = 1) (hb : d309941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43612 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308819 q = 1) (hb : d309930 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d308819, d309930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308819, d309930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43619 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d308820 q = 1) (hb : d309931 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d308820, d309931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d308820, d309931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308821 q = 1) (hb : d309939 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d308821, d309939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308821, d309939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308822 q = 1) (hb : d309940 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d308822, d309940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d308822, d309940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309636 q = 1) (hb : d309941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309636, d309941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309636, d309941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80557 (p : Pattern) (ha : d309647 p = 1) (hb : d309951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309643 q = 1) (hb : d309947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309643, d309947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309643, d309947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d43812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309644 q = 1) (hb : d309948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309644, d309948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309644, d309948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309645 q = 1) (hb : d309949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309645, d309949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309645, d309949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309646 q = 1) (hb : d309950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309646, d309950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309646, d309950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309647 q = 1) (hb : d309951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309647, d309951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309647, d309951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80558 (p : Pattern) (ha : d309653 p = 1) (hb : d309957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43387 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308824 q = 1) (hb : d309935 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d308824, d309935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80554 q ha hb
    | true =>
      simp only [d308824, d309935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80555 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d308825 q = 1) (hb : d309936 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d308825, d309936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d308825, d309936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309634 q = 1) (hb : d309937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309634, d309937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309634, d309937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309635 q = 1) (hb : d309938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309635, d309938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309635, d309938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309637 q = 1) (hb : d309942 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309637, d309942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309637, d309942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80556 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43646 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309638 q = 1) (hb : d309943 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309638, d309943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309638, d309943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309639 q = 1) (hb : d309944 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309639, d309944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309639, d309944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309640 q = 1) (hb : d309945 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309640, d309945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309640, d309945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309641 q = 1) (hb : d309946 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309641, d309946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309641, d309946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309648 q = 1) (hb : d309952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309648, d309952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309648, d309952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80557 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d43828 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309649 q = 1) (hb : d309953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309649, d309953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309649, d309953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309650 q = 1) (hb : d309954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309650, d309954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309650, d309954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309651 q = 1) (hb : d309955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309651, d309955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309651, d309955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309652 q = 1) (hb : d309956 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309652, d309956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309652, d309956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309653 q = 1) (hb : d309957 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309653, d309957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309653, d309957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80559 (p : Pattern) (ha : d309659 p = 1) (hb : d309963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309654 q = 1) (hb : d309958 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309654, d309958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309654, d309958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80558 q ha hb
  have h2 (q : Pattern) (ha : d309655 q = 1) (hb : d309959 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309655, d309959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309655, d309959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309656 q = 1) (hb : d309960 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309656, d309960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309656, d309960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309657 q = 1) (hb : d309961 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309657, d309961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309657, d309961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309658 q = 1) (hb : d309962 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309658, d309962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309658, d309962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309659 q = 1) (hb : d309963 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309659, d309963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309659, d309963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80560 (p : Pattern) (ha : d309183 p = 1) (hb : d309971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309179 q = 1) (hb : d309967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309179, d309967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309179, d309967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d309180 q = 1) (hb : d309968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309180, d309968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309180, d309968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309181 q = 1) (hb : d309969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309181, d309969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309181, d309969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309182 q = 1) (hb : d309970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309182, d309970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309182, d309970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309183 q = 1) (hb : d309971 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309183, d309971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309183, d309971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80561 (p : Pattern) (ha : d309193 p = 1) (hb : d309976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43980 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d43989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44040 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d309178 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d309179 q = 1) (hb : d309967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309179, d309967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309179, d309967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d44181 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d309180 q = 1) (hb : d309968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309180, d309968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309180, d309968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309181 q = 1) (hb : d309969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309181, d309969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309181, d309969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309182 q = 1) (hb : d309970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309182, d309970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309182, d309970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d44191 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d44196 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d309189 q = 1) (hb : d309972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309189, d309972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309189, d309972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309190 q = 1) (hb : d309973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309190, d309973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309190, d309973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309191 q = 1) (hb : d309974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309191, d309974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309191, d309974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d309192 q = 1) (hb : d309975 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309192, d309975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309192, d309975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d309193 q = 1) (hb : d309976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309193, d309976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309193, d309976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80562 (p : Pattern) (ha : d309665 p = 1) (hb : d309983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44198 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309188 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309189 q = 1) (hb : d309972 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309189, d309972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309189, d309972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44205 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309190 q = 1) (hb : d309973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309190, d309973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309190, d309973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309191 q = 1) (hb : d309981 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309191, d309981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309191, d309981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309192 q = 1) (hb : d309982 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309192, d309982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309192, d309982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309665 q = 1) (hb : d309983 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309665, d309983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309665, d309983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80563 (p : Pattern) (ha : d309676 p = 1) (hb : d309993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d44325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309671 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309672 q = 1) (hb : d309989 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309672, d309989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309672, d309989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d44409 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309673 q = 1) (hb : d309990 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309673, d309990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309673, d309990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309674 q = 1) (hb : d309991 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309674, d309991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309674, d309991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309675 q = 1) (hb : d309992 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309675, d309992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309675, d309992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d309676 q = 1) (hb : d309993 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309676, d309993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309676, d309993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80564 (p : Pattern) (ha : d309682 p = 1) (hb : d309999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d43972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309194 q = 1) (hb : d309977 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309194, d309977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80560 q ha hb
    | true =>
      simp only [d309194, d309977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80561 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d44223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309195 q = 1) (hb : d309978 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309195, d309978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309195, d309978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309663 q = 1) (hb : d309979 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309663, d309979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309663, d309979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309664 q = 1) (hb : d309980 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309664, d309980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309664, d309980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309666 q = 1) (hb : d309984 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309666, d309984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309666, d309984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80562 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d44232 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d309667 q = 1) (hb : d309985 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309667, d309985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309667, d309985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309668 q = 1) (hb : d309986 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309668, d309986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309668, d309986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d309669 q = 1) (hb : d309987 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309669, d309987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309669, d309987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d309670 q = 1) (hb : d309988 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309670, d309988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309670, d309988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309677 q = 1) (hb : d309994 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309677, d309994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309677, d309994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80563 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d44425 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d309678 q = 1) (hb : d309995 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309678, d309995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309678, d309995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d309679 q = 1) (hb : d309996 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309679, d309996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309679, d309996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d309680 q = 1) (hb : d309997 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309680, d309997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309680, d309997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d309681 q = 1) (hb : d309998 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309681, d309998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309681, d309998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d309682 q = 1) (hb : d309999 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309682, d309999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309682, d309999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80565 (p : Pattern) (ha : d309688 p = 1) (hb : d310005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309683 q = 1) (hb : d310000 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309683, d310000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309683, d310000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80564 q ha hb
  have h2 (q : Pattern) (ha : d309684 q = 1) (hb : d310001 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309684, d310001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309684, d310001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d309685 q = 1) (hb : d310002 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309685, d310002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309685, d310002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309686 q = 1) (hb : d310003 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309686, d310003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309686, d310003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d309687 q = 1) (hb : d310004 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309687, d310004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309687, d310004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309688 q = 1) (hb : d310005 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309688, d310005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309688, d310005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80566 (p : Pattern) (ha : d309724 p = 1) (hb : d310011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d309605 q = 1) (hb : d309883 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309605, d309883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80541 q ha hb
    | true =>
      simp only [d309605, d309883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80547 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d309632 q = 1) (hb : d309923 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309632, d309923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309632, d309923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80553 q ha hb
  have h3 (q : Pattern) (ha : d309633 q = 1) (hb : d309924 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309633, d309924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d309633, d309924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d309660 q = 1) (hb : d309964 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309660, d309964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309660, d309964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80559 q ha hb
  have h5 (q : Pattern) (ha : d309661 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309661, d309965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309661, d309965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d309662 q = 1) (hb : d309966 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309662, d309966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309662, d309966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d309689 q = 1) (hb : d310006 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309689, d310006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309689, d310006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80565 q ha hb
  have h8 (q : Pattern) (ha : d309690 q = 1) (hb : d310007 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309690, d310007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309690, d310007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d309691 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309691, d310008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309691, d310008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d309692 q = 1) (hb : d310009 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309692, d310009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309692, d310009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d309506 q = 1) (hb : d309719 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309506, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309506, d309719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80530 q ha hb
  have h12 (q : Pattern) (ha : d309507 q = 1) (hb : d309720 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309507, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309507, d309720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d309508 q = 1) (hb : d309721 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309508, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309508, d309721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d309509 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d309509, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309509, d309722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d309723 q = 1) (hb : d310010 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d309723, d310010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309723, d310010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d309724 q = 1) (hb : d310011 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d309724, d310011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309724, d310011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro80567 (p : Pattern) (ha : d309730 p = 1) (hb : d310017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309725 q = 1) (hb : d310012 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d309725, d310012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80566 q ha hb
    | true =>
      simp only [d309725, d310012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d309726 q = 1) (hb : d310013 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d309726, d310013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309726, d310013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d309727 q = 1) (hb : d310014 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d309727, d310014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309727, d310014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309728 q = 1) (hb : d310015 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d309728, d310015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309728, d310015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309729 q = 1) (hb : d310016 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d309729, d310016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309729, d310016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309730 q = 1) (hb : d310017 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d309730, d310017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309730, d310017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80568 (p : Pattern) (ha : d309736 p = 1) (hb : d310023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309731 q = 1) (hb : d310018 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d309731, d310018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80567 q ha hb
    | true =>
      simp only [d309731, d310018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d309732 q = 1) (hb : d310019 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d309732, d310019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309732, d310019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d309733 q = 1) (hb : d310020 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d309733, d310020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309733, d310020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309734 q = 1) (hb : d310021 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d309734, d310021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309734, d310021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309735 q = 1) (hb : d310022 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d309735, d310022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309735, d310022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309736 q = 1) (hb : d310023 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d309736, d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309736, d310023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80569 (p : Pattern) (ha : d309742 p = 1) (hb : d310029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309737 q = 1) (hb : d310024 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d309737, d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80568 q ha hb
    | true =>
      simp only [d309737, d310024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d309738 q = 1) (hb : d310025 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d309738, d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309738, d310025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d309739 q = 1) (hb : d310026 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d309739, d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309739, d310026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309740 q = 1) (hb : d310027 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d309740, d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309740, d310027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309741 q = 1) (hb : d310028 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d309741, d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309741, d310028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309742 q = 1) (hb : d310029 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d309742, d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309742, d310029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80570 (p : Pattern) (ha : d309748 p = 1) (hb : d310035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309743 q = 1) (hb : d310030 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d309743, d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80569 q ha hb
    | true =>
      simp only [d309743, d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d309744 q = 1) (hb : d310031 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d309744, d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309744, d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d309745 q = 1) (hb : d310032 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d309745, d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309745, d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309746 q = 1) (hb : d310033 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d309746, d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309746, d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309747 q = 1) (hb : d310034 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d309747, d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309747, d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309748 q = 1) (hb : d310035 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d309748, d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309748, d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80571 (p : Pattern) (ha : d309754 p = 1) (hb : d310041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309749 q = 1) (hb : d310036 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d309749, d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80570 q ha hb
    | true =>
      simp only [d309749, d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d309750 q = 1) (hb : d310037 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d309750, d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309750, d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d309751 q = 1) (hb : d310038 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d309751, d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309751, d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309752 q = 1) (hb : d310039 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d309752, d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309752, d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309753 q = 1) (hb : d310040 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d309753, d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309753, d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309754 q = 1) (hb : d310041 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d309754, d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309754, d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80572 (p : Pattern) (ha : d309760 p = 1) (hb : d310047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309755 q = 1) (hb : d310042 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d309755, d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80571 q ha hb
    | true =>
      simp only [d309755, d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d309756 q = 1) (hb : d310043 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d309756, d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309756, d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d309757 q = 1) (hb : d310044 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d309757, d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309757, d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309758 q = 1) (hb : d310045 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d309758, d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309758, d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309759 q = 1) (hb : d310046 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d309759, d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309759, d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309760 q = 1) (hb : d310047 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d309760, d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309760, d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80573 (p : Pattern) (ha : d309766 p = 1) (hb : d310053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309761 q = 1) (hb : d310048 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d309761, d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80572 q ha hb
    | true =>
      simp only [d309761, d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d309762 q = 1) (hb : d310049 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d309762, d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309762, d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d309763 q = 1) (hb : d310050 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d309763, d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309763, d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d309764 q = 1) (hb : d310051 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d309764, d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309764, d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d309765 q = 1) (hb : d310052 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d309765, d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309765, d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d309766 q = 1) (hb : d310053 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d309766, d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309766, d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80574 (p : Pattern) (ha : d31626 p = 1) (hb : d310056 p = 1) : d31312 p = 1 := by
  have h0 (q : Pattern) (ha : d31308 q = 1) (hb : d310056 q = 1) : d31308 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30968 q = 1) (hb : d310056 q = 1) : d30968 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31621 q = 1) (hb : d310056 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d310056 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d310056 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31309 q = 1) (hb : d310056 q = 1) : d31309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31624 q = 1) (hb : d310056 q = 1) : d31310 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31624, d31310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31624, d31310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31625 q = 1) (hb : d310056 q = 1) : d31311 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31625, d31311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31625, d31311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d31626 q = 1) (hb : d310056 q = 1) : d31312 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31626, d31312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31626, d31312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80575 (p : Pattern) (ha : d31636 p = 1) (hb : d310056 p = 1) : d31317 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d310056 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31621 q = 1) (hb : d310056 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31622 q = 1) (hb : d310056 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31623 q = 1) (hb : d310056 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30973 q = 1) (hb : d310056 q = 1) : d30973 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31631 q = 1) (hb : d310056 q = 1) : d30974 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31631, d30974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31631, d30974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31632 q = 1) (hb : d310056 q = 1) : d30975 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31632, d30975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31632, d30975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d25434 q = 1) (hb : d310056 q = 1) : d25434 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31633 q = 1) (hb : d310056 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31634 q = 1) (hb : d310056 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d31635 q = 1) (hb : d310056 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d31636 q = 1) (hb : d310056 q = 1) : d31317 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31636, d31317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31636, d31317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro80576 (p : Pattern) (ha : d31642 p = 1) (hb : d310056 p = 1) : d31325 p = 1 := by
  have h0 (q : Pattern) (ha : d31324 q = 1) (hb : d310056 q = 1) : d31324 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31621 q = 1) (hb : d310056 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31622 q = 1) (hb : d310056 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25434 q = 1) (hb : d310056 q = 1) : d25434 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d31633 q = 1) (hb : d310056 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31634 q = 1) (hb : d310056 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d31635 q = 1) (hb : d310056 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d31642 q = 1) (hb : d310056 q = 1) : d31325 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31642, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31642, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro80577 (p : Pattern) (ha : d31649 p = 1) (hb : d310056 p = 1) : d310058 p = 1 := by
  have h0 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31621 q = 1) (hb : d310056 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31622 q = 1) (hb : d310056 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25434 q = 1) (hb : d310056 q = 1) : d25434 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31633 q = 1) (hb : d310056 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25435 q = 1) (hb : d310056 q = 1) : d25435 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31647 q = 1) (hb : d310056 q = 1) : d281106 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31647, d281106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31647, d281106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31648 q = 1) (hb : d310056 q = 1) : d281107 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31648, d281107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31648, d281107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d1119 q = 1) (hb : d310056 q = 1) : d1119 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31649 q = 1) (hb : d310056 q = 1) : d310058 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31649, d310058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31649, d310058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80578 (p : Pattern) (ha : d31655 p = 1) (hb : d310056 p = 1) : d310064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31627 q = 1) (hb : d310056 q = 1) : d31313 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31627, d31313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80574 q ha hb
    | true =>
      simp only [d31627, d31313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31628 q = 1) (hb : d310056 q = 1) : d31314 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31628, d31314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31628, d31314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31629 q = 1) (hb : d310056 q = 1) : d31315 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31629, d31315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31629, d31315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31630 q = 1) (hb : d310056 q = 1) : d31316 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31630, d31316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31630, d31316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31637 q = 1) (hb : d310056 q = 1) : d31318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31637, d31318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80575 q ha hb
    | true =>
      simp only [d31637, d31318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31638 q = 1) (hb : d310056 q = 1) : d31319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31638, d31319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31638, d31319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31639 q = 1) (hb : d310056 q = 1) : d31320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31639, d31320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31639, d31320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31640 q = 1) (hb : d310056 q = 1) : d31321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31640, d31321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31640, d31321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31641 q = 1) (hb : d310056 q = 1) : d31322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31641, d31322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31641, d31322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31643 q = 1) (hb : d310056 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80576 q ha hb
    | true =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31644 q = 1) (hb : d310056 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31645 q = 1) (hb : d310056 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31645, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31645, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31646 q = 1) (hb : d310056 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31646, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31646, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31650 q = 1) (hb : d310056 q = 1) : d310059 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
    | true =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31651 q = 1) (hb : d310056 q = 1) : d310060 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31652 q = 1) (hb : d310056 q = 1) : d310061 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d310061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d310061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31653 q = 1) (hb : d310056 q = 1) : d310062 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d310062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31653, d310062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31654 q = 1) (hb : d310056 q = 1) : d310063 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31654, d310063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31654, d310063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31655 q = 1) (hb : d310056 q = 1) : d310064 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31655, d310064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31655, d310064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80579 (p : Pattern) (ha : d31661 p = 1) (hb : d310056 p = 1) : d310068 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d310056 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31621 q = 1) (hb : d310056 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31622 q = 1) (hb : d310056 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31623 q = 1) (hb : d310056 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30973 q = 1) (hb : d310056 q = 1) : d30973 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31631 q = 1) (hb : d310056 q = 1) : d30974 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31631, d30974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31631, d30974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31632 q = 1) (hb : d310056 q = 1) : d30975 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31632, d30975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31632, d30975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d31657 q = 1) (hb : d310056 q = 1) : d31657 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31658 q = 1) (hb : d310056 q = 1) : d310065 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31658, d310065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31658, d310065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30635 q = 1) (hb : d310056 q = 1) : d30635 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d31659 q = 1) (hb : d310056 q = 1) : d310066 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31659, d310066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31659, d310066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31660 q = 1) (hb : d310056 q = 1) : d310067 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31660, d310067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31660, d310067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h14 (q : Pattern) (ha : d31661 q = 1) (hb : d310056 q = 1) : d310068 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31661, d310068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31661, d310068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro80580 (p : Pattern) (ha : d31666 p = 1) (hb : d310056 p = 1) : d310073 p = 1 := by
  have h0 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31621 q = 1) (hb : d310056 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31622 q = 1) (hb : d310056 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31657 q = 1) (hb : d310056 q = 1) : d31657 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31658 q = 1) (hb : d310056 q = 1) : d310065 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31658, d310065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31658, d310065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30635 q = 1) (hb : d310056 q = 1) : d30635 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31659 q = 1) (hb : d310056 q = 1) : d310066 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31659, d310066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31659, d310066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31660 q = 1) (hb : d310056 q = 1) : d310067 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31660, d310067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31660, d310067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d1119 q = 1) (hb : d310056 q = 1) : d1119 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31666 q = 1) (hb : d310056 q = 1) : d310073 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31666, d310073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31666, d310073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80581 (p : Pattern) (ha : d31673 p = 1) (hb : d310056 p = 1) : d310080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31662 q = 1) (hb : d310056 q = 1) : d310069 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31662, d310069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80579 q ha hb
    | true =>
      simp only [d31662, d310069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31663 q = 1) (hb : d310056 q = 1) : d310070 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31663, d310070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31663, d310070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31664 q = 1) (hb : d310056 q = 1) : d310071 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31664, d310071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31664, d310071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31665 q = 1) (hb : d310056 q = 1) : d310072 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31665, d310072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31665, d310072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31667 q = 1) (hb : d310056 q = 1) : d310074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
    | true =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31668 q = 1) (hb : d310056 q = 1) : d310075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31669 q = 1) (hb : d310056 q = 1) : d310076 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d310076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d310076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31670 q = 1) (hb : d310056 q = 1) : d310077 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d310077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31670, d310077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31671 q = 1) (hb : d310056 q = 1) : d310078 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31671, d310078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31671, d310078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31650 q = 1) (hb : d310056 q = 1) : d310059 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
    | true =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31651 q = 1) (hb : d310056 q = 1) : d310060 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31652 q = 1) (hb : d310056 q = 1) : d310061 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d310061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d310061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31653 q = 1) (hb : d310056 q = 1) : d310062 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d310062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31653, d310062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31672 q = 1) (hb : d310056 q = 1) : d310079 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31672, d310079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31672, d310079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31673 q = 1) (hb : d310056 q = 1) : d310080 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31673, d310080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31673, d310080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80582 (p : Pattern) (ha : d31678 p = 1) (hb : d310056 p = 1) : d310085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31667 q = 1) (hb : d310056 q = 1) : d310074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
    | true =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31668 q = 1) (hb : d310056 q = 1) : d310075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31669 q = 1) (hb : d310056 q = 1) : d310076 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d310076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d310076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31670 q = 1) (hb : d310056 q = 1) : d310077 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d310077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31670, d310077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31677 q = 1) (hb : d310056 q = 1) : d310084 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31677, d310084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31677, d310084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d310056 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31678 q = 1) (hb : d310056 q = 1) : d310085 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31678, d310085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31678, d310085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro80583 (p : Pattern) (ha : d31685 p = 1) (hb : d310056 p = 1) : d310092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31674 q = 1) (hb : d310056 q = 1) : d310081 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d310081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80578 q ha hb
    | true =>
      simp only [d31674, d310081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80581 q ha hb
  have h2 (q : Pattern) (ha : d31675 q = 1) (hb : d310056 q = 1) : d310082 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d310082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d310082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31676 q = 1) (hb : d310056 q = 1) : d310083 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d310083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d310083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31679 q = 1) (hb : d310056 q = 1) : d310086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d310086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80581 q ha hb
    | true =>
      simp only [d31679, d310086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80582 q ha hb
  have h5 (q : Pattern) (ha : d31680 q = 1) (hb : d310056 q = 1) : d310087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d310087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d310087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31681 q = 1) (hb : d310056 q = 1) : d310088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d310088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d310088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31682 q = 1) (hb : d310056 q = 1) : d310089 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d310089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31682, d310089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31683 q = 1) (hb : d310056 q = 1) : d310090 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31683, d310090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31683, d310090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31684 q = 1) (hb : d310056 q = 1) : d310091 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31684, d310091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31684, d310091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31685 q = 1) (hb : d310056 q = 1) : d310092 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31685, d310092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31685, d310092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro80584 (p : Pattern) (ha : d31689 p = 1) (hb : d310056 p = 1) : d310096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31679 q = 1) (hb : d310056 q = 1) : d310086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d310086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80581 q ha hb
    | true =>
      simp only [d31679, d310086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80582 q ha hb
  have h2 (q : Pattern) (ha : d31680 q = 1) (hb : d310056 q = 1) : d310087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d310087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d310087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31681 q = 1) (hb : d310056 q = 1) : d310088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d310088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d310088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31683 q = 1) (hb : d310056 q = 1) : d310090 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31683, d310090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31683, d310090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31688 q = 1) (hb : d310056 q = 1) : d310095 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31688, d310095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31688, d310095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31689 q = 1) (hb : d310056 q = 1) : d310096 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31689, d310096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31689, d310096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80585 (p : Pattern) (ha : d31695 p = 1) (hb : d310056 p = 1) : d310102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d310056 q = 1) : d310093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80583 q ha hb
    | true =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d310056 q = 1) : d310094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d310056 q = 1) : d310099 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d310056 q = 1) : d310100 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d310100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d310100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31694 q = 1) (hb : d310056 q = 1) : d310101 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31694, d310101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31694, d310101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31695 q = 1) (hb : d310056 q = 1) : d310102 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31695, d310102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31695, d310102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80586 (p : Pattern) (ha : d31699 p = 1) (hb : d310056 p = 1) : d310106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d310056 q = 1) : d310103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d310056 q = 1) : d310104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d310104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d310104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31698 q = 1) (hb : d310056 q = 1) : d310105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31698, d310105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31698, d310105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31699 q = 1) (hb : d310056 q = 1) : d310106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31699, d310106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31699, d310106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80587 (p : Pattern) (ha : d31705 p = 1) (hb : d310056 p = 1) : d310112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d310056 q = 1) : d310107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80585 q ha hb
    | true =>
      simp only [d31700, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80586 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d310056 q = 1) : d310108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d310056 q = 1) : d310109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d310056 q = 1) : d310110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d310056 q = 1) : d310111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31705 q = 1) (hb : d310056 q = 1) : d310112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31705, d310112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31705, d310112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80588 (p : Pattern) (ha : d31708 p = 1) (hb : d310056 p = 1) : d310115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d310056 q = 1) : d310093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80583 q ha hb
    | true =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d310056 q = 1) : d310094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d310056 q = 1) : d310099 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d310056 q = 1) : d310100 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d310100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d310100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31694 q = 1) (hb : d310056 q = 1) : d310101 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31694, d310101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31694, d310101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31708 q = 1) (hb : d310056 q = 1) : d310115 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31708, d310115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31708, d310115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80589 (p : Pattern) (ha : d31709 p = 1) (hb : d310056 p = 1) : d310116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d310056 q = 1) : d310103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d310056 q = 1) : d310104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d310104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d310104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31698 q = 1) (hb : d310056 q = 1) : d310105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31698, d310105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31698, d310105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31709 q = 1) (hb : d310056 q = 1) : d310116 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31709, d310116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31709, d310116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80590 (p : Pattern) (ha : d31715 p = 1) (hb : d310056 p = 1) : d310122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d310056 q = 1) : d310107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80585 q ha hb
    | true =>
      simp only [d31700, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80586 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d310056 q = 1) : d310108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d310056 q = 1) : d310109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d310056 q = 1) : d310110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d310056 q = 1) : d310111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31710 q = 1) (hb : d310056 q = 1) : d310117 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31710, d310117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80588 q ha hb
    | true =>
      simp only [d31710, d310117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80589 q ha hb
  have h7 (q : Pattern) (ha : d31711 q = 1) (hb : d310056 q = 1) : d310118 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31711, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31711, d310118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31712 q = 1) (hb : d310056 q = 1) : d310119 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31712, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31712, d310119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31713 q = 1) (hb : d310056 q = 1) : d310120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31713, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31713, d310120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31714 q = 1) (hb : d310056 q = 1) : d310121 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31714, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31714, d310121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31715 q = 1) (hb : d310056 q = 1) : d310122 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31715, d310122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31715, d310122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80591 (p : Pattern) (ha : d31927 p = 1) (hb : d310056 p = 1) : d310207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d310056 q = 1) : d310107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80585 q ha hb
    | true =>
      simp only [d31700, d310107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80586 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d310056 q = 1) : d310108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d310108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d310056 q = 1) : d310109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d310109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d310056 q = 1) : d310110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d310110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d310056 q = 1) : d310111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d310111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31922 q = 1) (hb : d310056 q = 1) : d310202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31922, d310202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80586 q ha hb
    | true =>
      simp only [d31922, d310202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31923 q = 1) (hb : d310056 q = 1) : d310203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31923, d310203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31923, d310203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31924 q = 1) (hb : d310056 q = 1) : d310204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31924, d310204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31924, d310204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31925 q = 1) (hb : d310056 q = 1) : d310205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31925, d310205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31925, d310205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31926 q = 1) (hb : d310056 q = 1) : d310206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31926, d310206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31926, d310206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31927 q = 1) (hb : d310056 q = 1) : d310207 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31927, d310207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31927, d310207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80592 (p : Pattern) (ha : d31933 p = 1) (hb : d310056 p = 1) : d310213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31922 q = 1) (hb : d310056 q = 1) : d310202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31922, d310202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80586 q ha hb
    | true =>
      simp only [d31922, d310202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31923 q = 1) (hb : d310056 q = 1) : d310203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31923, d310203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31923, d310203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31924 q = 1) (hb : d310056 q = 1) : d310204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31924, d310204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31924, d310204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31925 q = 1) (hb : d310056 q = 1) : d310205 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31925, d310205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31925, d310205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31926 q = 1) (hb : d310056 q = 1) : d310206 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31926, d310206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31926, d310206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31928 q = 1) (hb : d310056 q = 1) : d310208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31928, d310208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80589 q ha hb
    | true =>
      simp only [d31928, d310208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31929 q = 1) (hb : d310056 q = 1) : d310209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31929, d310209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31929, d310209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31930 q = 1) (hb : d310056 q = 1) : d310210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31930, d310210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31930, d310210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31931 q = 1) (hb : d310056 q = 1) : d310211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31931, d310211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31931, d310211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31932 q = 1) (hb : d310056 q = 1) : d310212 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31932, d310212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31932, d310212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31933 q = 1) (hb : d310056 q = 1) : d310213 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31933, d310213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31933, d310213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80593 (p : Pattern) (ha : d31942 p = 1) (hb : d310056 p = 1) : d310222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31928 q = 1) (hb : d310056 q = 1) : d310208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31928, d310208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80589 q ha hb
    | true =>
      simp only [d31928, d310208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31929 q = 1) (hb : d310056 q = 1) : d310209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31929, d310209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31929, d310209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31930 q = 1) (hb : d310056 q = 1) : d310210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31930, d310210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31930, d310210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31931 q = 1) (hb : d310056 q = 1) : d310211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31931, d310211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31931, d310211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31932 q = 1) (hb : d310056 q = 1) : d310212 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31932, d310212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31932, d310212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31942 q = 1) (hb : d310056 q = 1) : d310222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31942, d310222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31942, d310222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80594 (p : Pattern) (ha : d32005 p = 1) (hb : d310056 p = 1) : d310252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31996 q = 1) (hb : d310056 q = 1) : d310243 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31996, d310243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31996, d310243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80579 q ha hb
  have h2 (q : Pattern) (ha : d31662 q = 1) (hb : d310056 q = 1) : d310069 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31662, d310069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80579 q ha hb
    | true =>
      simp only [d31662, d310069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31997 q = 1) (hb : d310056 q = 1) : d310244 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31997, d310244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31997, d310244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31663 q = 1) (hb : d310056 q = 1) : d310070 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31663, d310070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31663, d310070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31998 q = 1) (hb : d310056 q = 1) : d310245 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31998, d310245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31998, d310245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31999 q = 1) (hb : d310056 q = 1) : d310246 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31999, d310246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31999, d310246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32000 q = 1) (hb : d310056 q = 1) : d310247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d310247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d310247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
  have h8 (q : Pattern) (ha : d31667 q = 1) (hb : d310056 q = 1) : d310074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
    | true =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32001 q = 1) (hb : d310056 q = 1) : d310248 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d310248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32001, d310248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31668 q = 1) (hb : d310056 q = 1) : d310075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32002 q = 1) (hb : d310056 q = 1) : d310249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d310249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32002, d310249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32003 q = 1) (hb : d310056 q = 1) : d310250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d310250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32003, d310250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32004 q = 1) (hb : d310056 q = 1) : d310251 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32004, d310251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32004, d310251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31976 q = 1) (hb : d310056 q = 1) : d310228 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d310228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d310228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
  have h15 (q : Pattern) (ha : d31650 q = 1) (hb : d310056 q = 1) : d310059 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
    | true =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31977 q = 1) (hb : d310056 q = 1) : d310229 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d310229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31977, d310229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31651 q = 1) (hb : d310056 q = 1) : d310060 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31978 q = 1) (hb : d310056 q = 1) : d310230 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d310230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31978, d310230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31979 q = 1) (hb : d310056 q = 1) : d310231 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d310231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31979, d310231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31990 q = 1) (hb : d310056 q = 1) : d310237 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31990, d310237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31990, d310237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d32005 q = 1) (hb : d310056 q = 1) : d310252 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32005, d310252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32005, d310252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro80595 (p : Pattern) (ha : d32010 p = 1) (hb : d310056 p = 1) : d310257 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32000 q = 1) (hb : d310056 q = 1) : d310247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d310247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d310247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
  have h2 (q : Pattern) (ha : d31667 q = 1) (hb : d310056 q = 1) : d310074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
    | true =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32001 q = 1) (hb : d310056 q = 1) : d310248 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d310248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32001, d310248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31668 q = 1) (hb : d310056 q = 1) : d310075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32002 q = 1) (hb : d310056 q = 1) : d310249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d310249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32002, d310249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32003 q = 1) (hb : d310056 q = 1) : d310250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d310250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32003, d310250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32009 q = 1) (hb : d310056 q = 1) : d310256 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32009, d310256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32009, d310256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15023 q = 1) (hb : d310056 q = 1) : d15023 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32010 q = 1) (hb : d310056 q = 1) : d310257 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32010, d310257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32010, d310257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro80596 (p : Pattern) (ha : d32029 p = 1) (hb : d310056 p = 1) : d310276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32011 q = 1) (hb : d310056 q = 1) : d310258 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d310258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80594 q ha hb
    | true =>
      simp only [d32011, d310258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80595 q ha hb
  have h2 (q : Pattern) (ha : d32012 q = 1) (hb : d310056 q = 1) : d310259 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d310259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d310259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32013 q = 1) (hb : d310056 q = 1) : d310260 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d310260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d310260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32019 q = 1) (hb : d310056 q = 1) : d310266 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32019, d310266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32019, d310266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32028 q = 1) (hb : d310056 q = 1) : d310275 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32028, d310275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32028, d310275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32029 q = 1) (hb : d310056 q = 1) : d310276 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32029, d310276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32029, d310276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80597 (p : Pattern) (ha : d32118 p = 1) (hb : d310056 p = 1) : d310308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32030 q = 1) (hb : d310056 q = 1) : d310277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32030, d310277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80596 q ha hb
    | true =>
      simp only [d32030, d310277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32031 q = 1) (hb : d310056 q = 1) : d310278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32031, d310278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32031, d310278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32115 q = 1) (hb : d310056 q = 1) : d310305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32115, d310305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32115, d310305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32116 q = 1) (hb : d310056 q = 1) : d310306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32116, d310306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32116, d310306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32117 q = 1) (hb : d310056 q = 1) : d310307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32117, d310307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32117, d310307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32118 q = 1) (hb : d310056 q = 1) : d310308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32118, d310308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32118, d310308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80598 (p : Pattern) (ha : d32124 p = 1) (hb : d310056 p = 1) : d310314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32119 q = 1) (hb : d310056 q = 1) : d310309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32119, d310309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80597 q ha hb
    | true =>
      simp only [d32119, d310309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32120 q = 1) (hb : d310056 q = 1) : d310310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32120, d310310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32120, d310310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32121 q = 1) (hb : d310056 q = 1) : d310311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32121, d310311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32121, d310311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32122 q = 1) (hb : d310056 q = 1) : d310312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32122, d310312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32122, d310312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32123 q = 1) (hb : d310056 q = 1) : d310313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32123, d310313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32123, d310313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32124 q = 1) (hb : d310056 q = 1) : d310314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32124, d310314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32124, d310314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80599 (p : Pattern) (ha : d31720 p = 1) (hb : d310056 p = 1) : d310127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d310056 q = 1) : d310093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80583 q ha hb
    | true =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d310056 q = 1) : d310094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d310056 q = 1) : d310099 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d310056 q = 1) : d310100 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d310100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d310100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31719 q = 1) (hb : d310056 q = 1) : d310126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31719, d310126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31719, d310126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31720 q = 1) (hb : d310056 q = 1) : d310127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31720, d310127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31720, d310127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80600 (p : Pattern) (ha : d31722 p = 1) (hb : d310056 p = 1) : d310129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d310056 q = 1) : d310103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d310056 q = 1) : d310104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d310104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d310104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31721 q = 1) (hb : d310056 q = 1) : d310128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31721, d310128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31721, d310128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31722 q = 1) (hb : d310056 q = 1) : d310129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31722, d310129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31722, d310129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80601 (p : Pattern) (ha : d31729 p = 1) (hb : d310056 p = 1) : d310136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d310056 q = 1) : d310093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80583 q ha hb
    | true =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d310056 q = 1) : d310094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d310056 q = 1) : d310099 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31727 q = 1) (hb : d310056 q = 1) : d310134 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31727, d310134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31727, d310134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31728 q = 1) (hb : d310056 q = 1) : d310135 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31728, d310135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31728, d310135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31729 q = 1) (hb : d310056 q = 1) : d310136 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31729, d310136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31729, d310136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80602 (p : Pattern) (ha : d31732 p = 1) (hb : d310056 p = 1) : d310139 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d310056 q = 1) : d310103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31730 q = 1) (hb : d310056 q = 1) : d310137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31730, d310137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31730, d310137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31731 q = 1) (hb : d310056 q = 1) : d310138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31731, d310138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31731, d310138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31732 q = 1) (hb : d310056 q = 1) : d310139 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31732, d310139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31732, d310139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80603 (p : Pattern) (ha : d31761 p = 1) (hb : d310056 p = 1) : d281185 p = 1 := by
  have h0 (q : Pattern) (ha : d31752 q = 1) (hb : d310056 q = 1) : d31752 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31759 q = 1) (hb : d310056 q = 1) : d31759 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31643 q = 1) (hb : d310056 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80576 q ha hb
    | true =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31644 q = 1) (hb : d310056 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d31645 q = 1) (hb : d310056 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31645, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31645, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31646 q = 1) (hb : d310056 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31646, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31646, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d31760 q = 1) (hb : d310056 q = 1) : d244181 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31760, d244181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31760, d244181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31761 q = 1) (hb : d310056 q = 1) : d281185 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31761, d281185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31761, d281185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80604 (p : Pattern) (ha : d31767 p = 1) (hb : d310056 p = 1) : d31325 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d310056 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31621 q = 1) (hb : d310056 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d310056, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31622 q = 1) (hb : d310056 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31623 q = 1) (hb : d310056 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31765 q = 1) (hb : d310056 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31765, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31765, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d31766 q = 1) (hb : d310056 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31766, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31766, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d25434 q = 1) (hb : d310056 q = 1) : d25434 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d31633 q = 1) (hb : d310056 q = 1) : d30747 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31633, d30747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31634 q = 1) (hb : d310056 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31634, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h11 (q : Pattern) (ha : d31635 q = 1) (hb : d310056 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31635, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d31767 q = 1) (hb : d310056 q = 1) : d31325 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31767, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31767, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80605 (p : Pattern) (ha : d31773 p = 1) (hb : d310056 p = 1) : d310146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31768 q = 1) (hb : d310056 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31768, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80604 q ha hb
    | true =>
      simp only [d31768, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31769 q = 1) (hb : d310056 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31769, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31769, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31770 q = 1) (hb : d310056 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31770, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31770, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31771 q = 1) (hb : d310056 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31771, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31771, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31650 q = 1) (hb : d310056 q = 1) : d310059 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
    | true =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31651 q = 1) (hb : d310056 q = 1) : d310060 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31652 q = 1) (hb : d310056 q = 1) : d310061 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d310061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d310061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31653 q = 1) (hb : d310056 q = 1) : d310062 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d310062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31653, d310062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31772 q = 1) (hb : d310056 q = 1) : d310063 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31772, d310063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31772, d310063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31672 q = 1) (hb : d310056 q = 1) : d310079 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31672, d310079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31672, d310079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31773 q = 1) (hb : d310056 q = 1) : d310146 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31773, d310146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31773, d310146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80606 (p : Pattern) (ha : d31779 p = 1) (hb : d310056 p = 1) : d310152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31762 q = 1) (hb : d310056 q = 1) : d310143 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31762, d310143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80603 q ha hb
    | true =>
      simp only [d31762, d310143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80578 q ha hb
  have h2 (q : Pattern) (ha : d31763 q = 1) (hb : d310056 q = 1) : d310144 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31763, d310144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31763, d310144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31764 q = 1) (hb : d310056 q = 1) : d310145 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31764, d310145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31764, d310145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31774 q = 1) (hb : d310056 q = 1) : d310147 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31774, d310147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80578 q ha hb
    | true =>
      simp only [d31774, d310147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80605 q ha hb
  have h5 (q : Pattern) (ha : d31775 q = 1) (hb : d310056 q = 1) : d310148 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31775, d310148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31775, d310148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31776 q = 1) (hb : d310056 q = 1) : d310149 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31776, d310149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31776, d310149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31777 q = 1) (hb : d310056 q = 1) : d310150 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31777, d310150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31777, d310150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31674 q = 1) (hb : d310056 q = 1) : d310081 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d310081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80578 q ha hb
    | true =>
      simp only [d31674, d310081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80581 q ha hb
  have h9 (q : Pattern) (ha : d31675 q = 1) (hb : d310056 q = 1) : d310082 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d310082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d310082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31676 q = 1) (hb : d310056 q = 1) : d310083 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d310083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d310083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31679 q = 1) (hb : d310056 q = 1) : d310086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d310086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80581 q ha hb
    | true =>
      simp only [d31679, d310086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80582 q ha hb
  have h12 (q : Pattern) (ha : d31680 q = 1) (hb : d310056 q = 1) : d310087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d310087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d310087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31681 q = 1) (hb : d310056 q = 1) : d310088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d310088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d310088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31682 q = 1) (hb : d310056 q = 1) : d310089 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d310089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31682, d310089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31778 q = 1) (hb : d310056 q = 1) : d310151 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31778, d310151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31778, d310151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31779 q = 1) (hb : d310056 q = 1) : d310152 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31779, d310152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31779, d310152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro80607 (p : Pattern) (ha : d31785 p = 1) (hb : d310056 p = 1) : d310158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31780 q = 1) (hb : d310056 q = 1) : d310153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31780, d310153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80606 q ha hb
    | true =>
      simp only [d31780, d310153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31781 q = 1) (hb : d310056 q = 1) : d310154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31781, d310154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31781, d310154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31686 q = 1) (hb : d310056 q = 1) : d310093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80583 q ha hb
    | true =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31687 q = 1) (hb : d310056 q = 1) : d310094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31782 q = 1) (hb : d310056 q = 1) : d310155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31782, d310155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31782, d310155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31783 q = 1) (hb : d310056 q = 1) : d310156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31783, d310156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31783, d310156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31784 q = 1) (hb : d310056 q = 1) : d310157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31784, d310157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31784, d310157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31785 q = 1) (hb : d310056 q = 1) : d310158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31785, d310158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31785, d310158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80608 (p : Pattern) (ha : d31878 p = 1) (hb : d310056 p = 1) : d310161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31667 q = 1) (hb : d310056 q = 1) : d310074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
    | true =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31668 q = 1) (hb : d310056 q = 1) : d310075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31669 q = 1) (hb : d310056 q = 1) : d310076 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d310076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d310076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31670 q = 1) (hb : d310056 q = 1) : d310077 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d310077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31670, d310077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31677 q = 1) (hb : d310056 q = 1) : d310084 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31677, d310084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31677, d310084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31878 q = 1) (hb : d310056 q = 1) : d310161 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31878, d310161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31878, d310161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80609 (p : Pattern) (ha : d31884 p = 1) (hb : d310056 p = 1) : d310167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31674 q = 1) (hb : d310056 q = 1) : d310081 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d310081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80578 q ha hb
    | true =>
      simp only [d31674, d310081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80581 q ha hb
  have h2 (q : Pattern) (ha : d31675 q = 1) (hb : d310056 q = 1) : d310082 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d310082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d310082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31676 q = 1) (hb : d310056 q = 1) : d310083 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d310083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d310083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31679 q = 1) (hb : d310056 q = 1) : d310086 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d310086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80581 q ha hb
    | true =>
      simp only [d31679, d310086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80582 q ha hb
  have h5 (q : Pattern) (ha : d31680 q = 1) (hb : d310056 q = 1) : d310087 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d310087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d310087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31681 q = 1) (hb : d310056 q = 1) : d310088 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d310088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d310088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31682 q = 1) (hb : d310056 q = 1) : d310089 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d310089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31682, d310089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31879 q = 1) (hb : d310056 q = 1) : d310162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31879, d310162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80581 q ha hb
    | true =>
      simp only [d31879, d310162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80608 q ha hb
  have h9 (q : Pattern) (ha : d31880 q = 1) (hb : d310056 q = 1) : d310163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31880, d310163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31880, d310163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31881 q = 1) (hb : d310056 q = 1) : d310164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31881, d310164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31881, d310164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31882 q = 1) (hb : d310056 q = 1) : d310165 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31882, d310165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31882, d310165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31883 q = 1) (hb : d310056 q = 1) : d310166 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31883, d310166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31883, d310166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31884 q = 1) (hb : d310056 q = 1) : d310167 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31884, d310167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31884, d310167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro80610 (p : Pattern) (ha : d31890 p = 1) (hb : d310056 p = 1) : d310173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31885 q = 1) (hb : d310056 q = 1) : d310168 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31885, d310168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80609 q ha hb
    | true =>
      simp only [d31885, d310168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31886 q = 1) (hb : d310056 q = 1) : d310169 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31886, d310169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31886, d310169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31887 q = 1) (hb : d310056 q = 1) : d310170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31887, d310170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31887, d310170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31888 q = 1) (hb : d310056 q = 1) : d310171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31888, d310171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31888, d310171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31889 q = 1) (hb : d310056 q = 1) : d310172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31889, d310172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31889, d310172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31890 q = 1) (hb : d310056 q = 1) : d310173 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31890, d310173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31890, d310173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80611 (p : Pattern) (ha : d245512 p = 1) (hb : d310056 p = 1) : d310179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31723 q = 1) (hb : d310056 q = 1) : d310130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31723, d310130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80599 q ha hb
    | true =>
      simp only [d31723, d310130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80600 q ha hb
  have h2 (q : Pattern) (ha : d31724 q = 1) (hb : d310056 q = 1) : d310131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31724, d310131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31724, d310131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31725 q = 1) (hb : d310056 q = 1) : d310132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31725, d310132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31725, d310132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31726 q = 1) (hb : d310056 q = 1) : d310133 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31726, d310133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31726, d310133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31733 q = 1) (hb : d310056 q = 1) : d310140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31733, d310140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80601 q ha hb
    | true =>
      simp only [d31733, d310140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80602 q ha hb
  have h6 (q : Pattern) (ha : d31734 q = 1) (hb : d310056 q = 1) : d310141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31734, d310141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31734, d310141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31735 q = 1) (hb : d310056 q = 1) : d310142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31735, d310142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31735, d310142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31786 q = 1) (hb : d310056 q = 1) : d310159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31786, d310159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80607 q ha hb
    | true =>
      simp only [d31786, d310159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80585 q ha hb
  have h9 (q : Pattern) (ha : d245508 q = 1) (hb : d310056 q = 1) : d310160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d310160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245508, d310160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31891 q = 1) (hb : d310056 q = 1) : d310174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31891, d310174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80610 q ha hb
    | true =>
      simp only [d31891, d310174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31892 q = 1) (hb : d310056 q = 1) : d310175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31892, d310175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31892, d310175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245509 q = 1) (hb : d310056 q = 1) : d310176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d310176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245509, d310176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245510 q = 1) (hb : d310056 q = 1) : d310177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d310177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245510, d310177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245511 q = 1) (hb : d310056 q = 1) : d310178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d310178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245511, d310178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245512 q = 1) (hb : d310056 q = 1) : d310179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d310179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245512, d310179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80612 (p : Pattern) (ha : d31897 p = 1) (hb : d310056 p = 1) : d310180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d310056 q = 1) : d310093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80583 q ha hb
    | true =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d310056 q = 1) : d310094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d310056 q = 1) : d310099 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d310056 q = 1) : d310100 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d310100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d310100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31719 q = 1) (hb : d310056 q = 1) : d310126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31719, d310126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31719, d310126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31897 q = 1) (hb : d310056 q = 1) : d310180 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31897, d310180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31897, d310180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80613 (p : Pattern) (ha : d31898 p = 1) (hb : d310056 p = 1) : d310181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d310056 q = 1) : d310103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d310056 q = 1) : d310104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d310104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d310104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31721 q = 1) (hb : d310056 q = 1) : d310128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31721, d310128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31721, d310128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31898 q = 1) (hb : d310056 q = 1) : d310181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31898, d310181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31898, d310181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80614 (p : Pattern) (ha : d31903 p = 1) (hb : d310056 p = 1) : d310186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d310056 q = 1) : d310093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80583 q ha hb
    | true =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d310056 q = 1) : d310094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d310056 q = 1) : d310099 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d310099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31727 q = 1) (hb : d310056 q = 1) : d310134 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31727, d310134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31727, d310134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31728 q = 1) (hb : d310056 q = 1) : d310135 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31728, d310135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31728, d310135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31903 q = 1) (hb : d310056 q = 1) : d310186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31903, d310186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31903, d310186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80615 (p : Pattern) (ha : d31904 p = 1) (hb : d310056 p = 1) : d310187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d310056 q = 1) : d310097 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80584 q ha hb
    | true =>
      simp only [d31690, d310097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d310056 q = 1) : d310098 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d310098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d310056 q = 1) : d310103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d310103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31730 q = 1) (hb : d310056 q = 1) : d310137 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31730, d310137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31730, d310137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31731 q = 1) (hb : d310056 q = 1) : d310138 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31731, d310138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31731, d310138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31904 q = 1) (hb : d310056 q = 1) : d310187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31904, d310187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31904, d310187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80616 (p : Pattern) (ha : d31908 p = 1) (hb : d310056 p = 1) : d310191 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31780 q = 1) (hb : d310056 q = 1) : d310153 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31780, d310153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80606 q ha hb
    | true =>
      simp only [d31780, d310153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31781 q = 1) (hb : d310056 q = 1) : d310154 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31781, d310154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31781, d310154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31686 q = 1) (hb : d310056 q = 1) : d310093 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80583 q ha hb
    | true =>
      simp only [d31686, d310093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31687 q = 1) (hb : d310056 q = 1) : d310094 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d310094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31782 q = 1) (hb : d310056 q = 1) : d310155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31782, d310155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31782, d310155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31783 q = 1) (hb : d310056 q = 1) : d310156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31783, d310156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31783, d310156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31784 q = 1) (hb : d310056 q = 1) : d310157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31784, d310157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31784, d310157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31908 q = 1) (hb : d310056 q = 1) : d310191 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31908, d310191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31908, d310191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80617 (p : Pattern) (ha : d31914 p = 1) (hb : d310056 p = 1) : d310194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31885 q = 1) (hb : d310056 q = 1) : d310168 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31885, d310168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80609 q ha hb
    | true =>
      simp only [d31885, d310168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31886 q = 1) (hb : d310056 q = 1) : d310169 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31886, d310169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31886, d310169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31887 q = 1) (hb : d310056 q = 1) : d310170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31887, d310170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31887, d310170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31888 q = 1) (hb : d310056 q = 1) : d310171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31888, d310171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31888, d310171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31889 q = 1) (hb : d310056 q = 1) : d310172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31889, d310172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31889, d310172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31914 q = 1) (hb : d310056 q = 1) : d310194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31914, d310194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31914, d310194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80618 (p : Pattern) (ha : d245517 p = 1) (hb : d310056 p = 1) : d310200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31723 q = 1) (hb : d310056 q = 1) : d310130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31723, d310130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80599 q ha hb
    | true =>
      simp only [d31723, d310130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80600 q ha hb
  have h2 (q : Pattern) (ha : d31724 q = 1) (hb : d310056 q = 1) : d310131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31724, d310131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31724, d310131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31725 q = 1) (hb : d310056 q = 1) : d310132 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31725, d310132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31725, d310132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31726 q = 1) (hb : d310056 q = 1) : d310133 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31726, d310133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31726, d310133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31733 q = 1) (hb : d310056 q = 1) : d310140 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31733, d310140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80601 q ha hb
    | true =>
      simp only [d31733, d310140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80602 q ha hb
  have h6 (q : Pattern) (ha : d31734 q = 1) (hb : d310056 q = 1) : d310141 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31734, d310141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31734, d310141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31735 q = 1) (hb : d310056 q = 1) : d310142 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31735, d310142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31735, d310142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31786 q = 1) (hb : d310056 q = 1) : d310159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31786, d310159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80607 q ha hb
    | true =>
      simp only [d31786, d310159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80585 q ha hb
  have h9 (q : Pattern) (ha : d245508 q = 1) (hb : d310056 q = 1) : d310160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d310160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245508, d310160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31891 q = 1) (hb : d310056 q = 1) : d310174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31891, d310174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80610 q ha hb
    | true =>
      simp only [d31891, d310174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31892 q = 1) (hb : d310056 q = 1) : d310175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31892, d310175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31892, d310175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245509 q = 1) (hb : d310056 q = 1) : d310176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d310176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245509, d310176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245510 q = 1) (hb : d310056 q = 1) : d310177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d310177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245510, d310177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245511 q = 1) (hb : d310056 q = 1) : d310178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d310178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245511, d310178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31899 q = 1) (hb : d310056 q = 1) : d310182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31899, d310182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80612 q ha hb
    | true =>
      simp only [d31899, d310182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80613 q ha hb
  have h16 (q : Pattern) (ha : d31900 q = 1) (hb : d310056 q = 1) : d310183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31900, d310183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31900, d310183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31901 q = 1) (hb : d310056 q = 1) : d310184 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31901, d310184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31901, d310184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31902 q = 1) (hb : d310056 q = 1) : d310185 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31902, d310185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31902, d310185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31905 q = 1) (hb : d310056 q = 1) : d310188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31905, d310188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80614 q ha hb
    | true =>
      simp only [d31905, d310188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80615 q ha hb
  have h20 (q : Pattern) (ha : d31906 q = 1) (hb : d310056 q = 1) : d310189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31906, d310189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31906, d310189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31907 q = 1) (hb : d310056 q = 1) : d310190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31907, d310190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31907, d310190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31909 q = 1) (hb : d310056 q = 1) : d310192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31909, d310192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80616 q ha hb
    | true =>
      simp only [d31909, d310192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80588 q ha hb
  have h23 (q : Pattern) (ha : d245513 q = 1) (hb : d310056 q = 1) : d310193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d310193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245513, d310193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d31915 q = 1) (hb : d310056 q = 1) : d310195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31915, d310195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80617 q ha hb
    | true =>
      simp only [d31915, d310195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d31916 q = 1) (hb : d310056 q = 1) : d310196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31916, d310196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31916, d310196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d245514 q = 1) (hb : d310056 q = 1) : d310197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d310197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245514, d310197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d245515 q = 1) (hb : d310056 q = 1) : d310198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245515, d310198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245515, d310198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d245516 q = 1) (hb : d310056 q = 1) : d310199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245516, d310199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245516, d310199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d245517 q = 1) (hb : d310056 q = 1) : d310200 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245517, d310200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245517, d310200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro80619 (p : Pattern) (ha : d245524 p = 1) (hb : d310056 p = 1) : d310220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31909 q = 1) (hb : d310056 q = 1) : d310192 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31909, d310192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80616 q ha hb
    | true =>
      simp only [d31909, d310192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80588 q ha hb
  have h2 (q : Pattern) (ha : d245513 q = 1) (hb : d310056 q = 1) : d310193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d310193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245513, d310193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31915 q = 1) (hb : d310056 q = 1) : d310195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31915, d310195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80617 q ha hb
    | true =>
      simp only [d31915, d310195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31916 q = 1) (hb : d310056 q = 1) : d310196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31916, d310196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31916, d310196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245514 q = 1) (hb : d310056 q = 1) : d310197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d310197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245514, d310197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245522 q = 1) (hb : d310056 q = 1) : d310218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245522, d310218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245522, d310218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245523 q = 1) (hb : d310056 q = 1) : d310219 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245523, d310219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245523, d310219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245524 q = 1) (hb : d310056 q = 1) : d310220 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245524, d310220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245524, d310220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80620 (p : Pattern) (ha : d31966 p = 1) (hb : d310056 p = 1) : d281271 p = 1 := by
  have h0 (q : Pattern) (ha : d31956 q = 1) (hb : d310056 q = 1) : d31956 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31960 q = 1) (hb : d310056 q = 1) : d31960 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31961 q = 1) (hb : d310056 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31961, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31961, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80576 q ha hb
  have h4 (q : Pattern) (ha : d31643 q = 1) (hb : d310056 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80576 q ha hb
    | true =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d31962 q = 1) (hb : d310056 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31962, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31962, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31644 q = 1) (hb : d310056 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d31963 q = 1) (hb : d310056 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31963, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31963, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31964 q = 1) (hb : d310056 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31964, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31964, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d31965 q = 1) (hb : d310056 q = 1) : d244255 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31965, d244255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31965, d244255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31966 q = 1) (hb : d310056 q = 1) : d281271 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31966, d281271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31966, d281271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80621 (p : Pattern) (ha : d31981 p = 1) (hb : d310056 p = 1) : d310233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31967 q = 1) (hb : d310056 q = 1) : d31475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31967, d31475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31967, d31475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80574 q ha hb
  have h2 (q : Pattern) (ha : d31627 q = 1) (hb : d310056 q = 1) : d31313 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31627, d31313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80574 q ha hb
    | true =>
      simp only [d31627, d31313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31968 q = 1) (hb : d310056 q = 1) : d31476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31968, d31476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31968, d31476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31628 q = 1) (hb : d310056 q = 1) : d31314 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31628, d31314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31628, d31314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31969 q = 1) (hb : d310056 q = 1) : d31477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31969, d31477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31969, d31477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31970 q = 1) (hb : d310056 q = 1) : d31478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31970, d31478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31970, d31478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31971 q = 1) (hb : d310056 q = 1) : d31479 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31971, d31479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31971, d31479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80575 q ha hb
  have h8 (q : Pattern) (ha : d31637 q = 1) (hb : d310056 q = 1) : d31318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31637, d31318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80575 q ha hb
    | true =>
      simp only [d31637, d31318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31972 q = 1) (hb : d310056 q = 1) : d31480 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31972, d31480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31972, d31480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31638 q = 1) (hb : d310056 q = 1) : d31319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31638, d31319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31638, d31319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31973 q = 1) (hb : d310056 q = 1) : d31481 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31973, d31481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31973, d31481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31974 q = 1) (hb : d310056 q = 1) : d31482 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31974, d31482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31974, d31482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31975 q = 1) (hb : d310056 q = 1) : d31483 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31975, d31483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31975, d31483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31961 q = 1) (hb : d310056 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31961, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31961, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80576 q ha hb
  have h15 (q : Pattern) (ha : d31643 q = 1) (hb : d310056 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80576 q ha hb
    | true =>
      simp only [d31643, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31962 q = 1) (hb : d310056 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31962, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31962, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31644 q = 1) (hb : d310056 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31644, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31963 q = 1) (hb : d310056 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31963, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31963, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31964 q = 1) (hb : d310056 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31964, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31964, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31976 q = 1) (hb : d310056 q = 1) : d310228 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d310228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d310228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
  have h21 (q : Pattern) (ha : d31650 q = 1) (hb : d310056 q = 1) : d310059 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
    | true =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31977 q = 1) (hb : d310056 q = 1) : d310229 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d310229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31977, d310229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d31651 q = 1) (hb : d310056 q = 1) : d310060 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d31978 q = 1) (hb : d310056 q = 1) : d310230 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d310230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d31978, d310230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d31979 q = 1) (hb : d310056 q = 1) : d310231 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d310231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31979, d310231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d31980 q = 1) (hb : d310056 q = 1) : d310232 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31980, d310232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31980, d310232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d31981 q = 1) (hb : d310056 q = 1) : d310233 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31981, d310233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31981, d310233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro80622 (p : Pattern) (ha : d31991 p = 1) (hb : d310056 p = 1) : d310238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31985 q = 1) (hb : d310056 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31985, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31985, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80604 q ha hb
  have h2 (q : Pattern) (ha : d31768 q = 1) (hb : d310056 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31768, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80604 q ha hb
    | true =>
      simp only [d31768, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31986 q = 1) (hb : d310056 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31986, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31986, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31769 q = 1) (hb : d310056 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31769, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31769, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31987 q = 1) (hb : d310056 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31987, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31987, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31988 q = 1) (hb : d310056 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31988, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31988, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31976 q = 1) (hb : d310056 q = 1) : d310228 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d310228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d310228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
  have h8 (q : Pattern) (ha : d31650 q = 1) (hb : d310056 q = 1) : d310059 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80577 q ha hb
    | true =>
      simp only [d31650, d310059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31977 q = 1) (hb : d310056 q = 1) : d310229 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d310229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31977, d310229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31651 q = 1) (hb : d310056 q = 1) : d310060 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31651, d310060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31978 q = 1) (hb : d310056 q = 1) : d310230 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d310230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31978, d310230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31979 q = 1) (hb : d310056 q = 1) : d310231 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d310231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31979, d310231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31989 q = 1) (hb : d310056 q = 1) : d310232 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31989, d310232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31989, d310232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31990 q = 1) (hb : d310056 q = 1) : d310237 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31990, d310237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31990, d310237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31991 q = 1) (hb : d310056 q = 1) : d310238 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31991, d310238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31991, d310238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80623 (p : Pattern) (ha : d32016 p = 1) (hb : d310056 p = 1) : d310263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31982 q = 1) (hb : d310056 q = 1) : d310234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31982, d310234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80620 q ha hb
    | true =>
      simp only [d31982, d310234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80621 q ha hb
  have h2 (q : Pattern) (ha : d31983 q = 1) (hb : d310056 q = 1) : d310235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31983, d310235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31983, d310235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31984 q = 1) (hb : d310056 q = 1) : d310236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31984, d310236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31984, d310236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31992 q = 1) (hb : d310056 q = 1) : d310239 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31992, d310239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80621 q ha hb
    | true =>
      simp only [d31992, d310239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80622 q ha hb
  have h5 (q : Pattern) (ha : d31993 q = 1) (hb : d310056 q = 1) : d310240 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31993, d310240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31993, d310240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31994 q = 1) (hb : d310056 q = 1) : d310241 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31994, d310241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31994, d310241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31995 q = 1) (hb : d310056 q = 1) : d310242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31995, d310242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31995, d310242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32006 q = 1) (hb : d310056 q = 1) : d310253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d310253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80621 q ha hb
    | true =>
      simp only [d32006, d310253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80594 q ha hb
  have h9 (q : Pattern) (ha : d32007 q = 1) (hb : d310056 q = 1) : d310254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d310254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d310254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32008 q = 1) (hb : d310056 q = 1) : d310255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d310255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d310255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32011 q = 1) (hb : d310056 q = 1) : d310258 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d310258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80594 q ha hb
    | true =>
      simp only [d32011, d310258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80595 q ha hb
  have h12 (q : Pattern) (ha : d32012 q = 1) (hb : d310056 q = 1) : d310259 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d310259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d310259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32013 q = 1) (hb : d310056 q = 1) : d310260 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d310260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d310260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32014 q = 1) (hb : d310056 q = 1) : d310261 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d310261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32014, d310261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32015 q = 1) (hb : d310056 q = 1) : d310262 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32015, d310262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32015, d310262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32016 q = 1) (hb : d310056 q = 1) : d310263 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32016, d310263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32016, d310263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro80624 (p : Pattern) (ha : d32021 p = 1) (hb : d310056 p = 1) : d310268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32006 q = 1) (hb : d310056 q = 1) : d310253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d310253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80621 q ha hb
    | true =>
      simp only [d32006, d310253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80594 q ha hb
  have h2 (q : Pattern) (ha : d32007 q = 1) (hb : d310056 q = 1) : d310254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d310254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d310254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32008 q = 1) (hb : d310056 q = 1) : d310255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d310255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d310255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32011 q = 1) (hb : d310056 q = 1) : d310258 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d310258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80594 q ha hb
    | true =>
      simp only [d32011, d310258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80595 q ha hb
  have h5 (q : Pattern) (ha : d32012 q = 1) (hb : d310056 q = 1) : d310259 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d310259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d310259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32013 q = 1) (hb : d310056 q = 1) : d310260 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d310260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d310260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32014 q = 1) (hb : d310056 q = 1) : d310261 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d310261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32014, d310261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32019 q = 1) (hb : d310056 q = 1) : d310266 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32019, d310266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32019, d310266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32020 q = 1) (hb : d310056 q = 1) : d310267 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32020, d310267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32020, d310267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32021 q = 1) (hb : d310056 q = 1) : d310268 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32021, d310268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32021, d310268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro80625 (p : Pattern) (ha : d32027 p = 1) (hb : d310056 p = 1) : d310274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32017 q = 1) (hb : d310056 q = 1) : d310264 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32017, d310264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80623 q ha hb
    | true =>
      simp only [d32017, d310264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32018 q = 1) (hb : d310056 q = 1) : d310265 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32018, d310265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32018, d310265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32022 q = 1) (hb : d310056 q = 1) : d310269 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32022, d310269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80624 q ha hb
    | true =>
      simp only [d32022, d310269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32023 q = 1) (hb : d310056 q = 1) : d310270 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32023, d310270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32023, d310270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32024 q = 1) (hb : d310056 q = 1) : d310271 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32024, d310271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32024, d310271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32025 q = 1) (hb : d310056 q = 1) : d310272 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32025, d310272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32025, d310272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32026 q = 1) (hb : d310056 q = 1) : d310273 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32026, d310273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32026, d310273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32027 q = 1) (hb : d310056 q = 1) : d310274 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32027, d310274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32027, d310274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80626 (p : Pattern) (ha : d32035 p = 1) (hb : d310056 p = 1) : d310282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32022 q = 1) (hb : d310056 q = 1) : d310269 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32022, d310269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80624 q ha hb
    | true =>
      simp only [d32022, d310269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32023 q = 1) (hb : d310056 q = 1) : d310270 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32023, d310270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32023, d310270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32030 q = 1) (hb : d310056 q = 1) : d310277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32030, d310277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80596 q ha hb
    | true =>
      simp only [d32030, d310277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32031 q = 1) (hb : d310056 q = 1) : d310278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32031, d310278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32031, d310278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32032 q = 1) (hb : d310056 q = 1) : d310279 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32032, d310279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32032, d310279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32033 q = 1) (hb : d310056 q = 1) : d310280 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32033, d310280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32033, d310280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32034 q = 1) (hb : d310056 q = 1) : d310281 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32034, d310281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32034, d310281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32035 q = 1) (hb : d310056 q = 1) : d310282 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32035, d310282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32035, d310282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80627 (p : Pattern) (ha : d32095 p = 1) (hb : d310056 p = 1) : d310285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32000 q = 1) (hb : d310056 q = 1) : d310247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d310247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d310247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
  have h2 (q : Pattern) (ha : d31667 q = 1) (hb : d310056 q = 1) : d310074 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80580 q ha hb
    | true =>
      simp only [d31667, d310074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32001 q = 1) (hb : d310056 q = 1) : d310248 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d310248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32001, d310248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31668 q = 1) (hb : d310056 q = 1) : d310075 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31668, d310075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32002 q = 1) (hb : d310056 q = 1) : d310249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d310249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32002, d310249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32003 q = 1) (hb : d310056 q = 1) : d310250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d310250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32003, d310250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32009 q = 1) (hb : d310056 q = 1) : d310256 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32009, d310256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32009, d310256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32095 q = 1) (hb : d310056 q = 1) : d310285 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32095, d310285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32095, d310285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80628 (p : Pattern) (ha : d32101 p = 1) (hb : d310056 p = 1) : d310291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32006 q = 1) (hb : d310056 q = 1) : d310253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d310253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80621 q ha hb
    | true =>
      simp only [d32006, d310253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80594 q ha hb
  have h2 (q : Pattern) (ha : d32007 q = 1) (hb : d310056 q = 1) : d310254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d310254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d310254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32008 q = 1) (hb : d310056 q = 1) : d310255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d310255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d310255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32011 q = 1) (hb : d310056 q = 1) : d310258 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d310258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80594 q ha hb
    | true =>
      simp only [d32011, d310258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80595 q ha hb
  have h5 (q : Pattern) (ha : d32012 q = 1) (hb : d310056 q = 1) : d310259 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d310259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d310259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32013 q = 1) (hb : d310056 q = 1) : d310260 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d310260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d310260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32014 q = 1) (hb : d310056 q = 1) : d310261 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d310261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32014, d310261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32096 q = 1) (hb : d310056 q = 1) : d310286 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32096, d310286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80594 q ha hb
    | true =>
      simp only [d32096, d310286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80627 q ha hb
  have h9 (q : Pattern) (ha : d32097 q = 1) (hb : d310056 q = 1) : d310287 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32097, d310287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32097, d310287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32098 q = 1) (hb : d310056 q = 1) : d310288 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32098, d310288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32098, d310288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32099 q = 1) (hb : d310056 q = 1) : d310289 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32099, d310289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32099, d310289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32100 q = 1) (hb : d310056 q = 1) : d310290 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32100, d310290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32100, d310290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32101 q = 1) (hb : d310056 q = 1) : d310291 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32101, d310291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32101, d310291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro80629 (p : Pattern) (ha : d32107 p = 1) (hb : d310056 p = 1) : d310297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32102 q = 1) (hb : d310056 q = 1) : d310292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32102, d310292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80628 q ha hb
    | true =>
      simp only [d32102, d310292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32103 q = 1) (hb : d310056 q = 1) : d310293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32103, d310293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32103, d310293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32104 q = 1) (hb : d310056 q = 1) : d310294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32104, d310294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32104, d310294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32105 q = 1) (hb : d310056 q = 1) : d310295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32105, d310295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32105, d310295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32106 q = 1) (hb : d310056 q = 1) : d310296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32106, d310296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32106, d310296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32107 q = 1) (hb : d310056 q = 1) : d310297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32107, d310297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32107, d310297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80630 (p : Pattern) (ha : d245534 p = 1) (hb : d310056 p = 1) : d310303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32036 q = 1) (hb : d310056 q = 1) : d310283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32036, d310283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80625 q ha hb
    | true =>
      simp only [d32036, d310283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80626 q ha hb
  have h2 (q : Pattern) (ha : d245530 q = 1) (hb : d310056 q = 1) : d310284 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245530, d310284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245530, d310284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32108 q = 1) (hb : d310056 q = 1) : d310298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32108, d310298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80629 q ha hb
    | true =>
      simp only [d32108, d310298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32109 q = 1) (hb : d310056 q = 1) : d310299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32109, d310299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32109, d310299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245531 q = 1) (hb : d310056 q = 1) : d310300 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245531, d310300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245531, d310300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245532 q = 1) (hb : d310056 q = 1) : d310301 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245532, d310301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245532, d310301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245533 q = 1) (hb : d310056 q = 1) : d310302 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245533, d310302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245533, d310302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245534 q = 1) (hb : d310056 q = 1) : d310303 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245534, d310303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245534, d310303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80631 (p : Pattern) (ha : d245540 p = 1) (hb : d310056 p = 1) : d310320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31706 q = 1) (hb : d310056 q = 1) : d310113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31706, d310113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31706, d310113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80587 q ha hb
  have h2 (q : Pattern) (ha : d31707 q = 1) (hb : d310056 q = 1) : d310114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31707, d310114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31707, d310114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31716 q = 1) (hb : d310056 q = 1) : d310123 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31716, d310123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80587 q ha hb
    | true =>
      simp only [d31716, d310123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80590 q ha hb
  have h4 (q : Pattern) (ha : d31717 q = 1) (hb : d310056 q = 1) : d310124 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31717, d310124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31717, d310124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31718 q = 1) (hb : d310056 q = 1) : d310125 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d31718, d310125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31718, d310125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245518 q = 1) (hb : d310056 q = 1) : d310201 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245518, d310201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80611 q ha hb
    | true =>
      simp only [d245518, d310201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80618 q ha hb
  have h7 (q : Pattern) (ha : d31934 q = 1) (hb : d310056 q = 1) : d310214 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31934, d310214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80591 q ha hb
    | true =>
      simp only [d31934, d310214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80592 q ha hb
  have h8 (q : Pattern) (ha : d245519 q = 1) (hb : d310056 q = 1) : d310215 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245519, d310215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245519, d310215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245520 q = 1) (hb : d310056 q = 1) : d310216 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245520, d310216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245520, d310216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d245521 q = 1) (hb : d310056 q = 1) : d310217 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245521, d310217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245521, d310217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245525 q = 1) (hb : d310056 q = 1) : d310221 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245525, d310221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245525, d310221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80619 q ha hb
  have h12 (q : Pattern) (ha : d31943 q = 1) (hb : d310056 q = 1) : d310223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31943, d310223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31943, d310223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80593 q ha hb
  have h13 (q : Pattern) (ha : d245526 q = 1) (hb : d310056 q = 1) : d310224 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245526, d310224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245526, d310224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245527 q = 1) (hb : d310056 q = 1) : d310225 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245527, d310225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245527, d310225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245528 q = 1) (hb : d310056 q = 1) : d310226 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245528, d310226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245528, d310226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d245529 q = 1) (hb : d310056 q = 1) : d310227 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245529, d310227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245529, d310227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245535 q = 1) (hb : d310056 q = 1) : d310304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245535, d310304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245535, d310304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80630 q ha hb
  have h18 (q : Pattern) (ha : d32125 q = 1) (hb : d310056 q = 1) : d310315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32125, d310315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32125, d310315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80598 q ha hb
  have h19 (q : Pattern) (ha : d245536 q = 1) (hb : d310056 q = 1) : d310316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245536, d310316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245536, d310316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d245537 q = 1) (hb : d310056 q = 1) : d310317 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245537, d310317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245537, d310317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d245538 q = 1) (hb : d310056 q = 1) : d310318 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245538, d310318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245538, d310318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d245539 q = 1) (hb : d310056 q = 1) : d310319 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245539, d310319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245539, d310319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d245540 q = 1) (hb : d310056 q = 1) : d310320 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245540, d310320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245540, d310320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro80632 (p : Pattern) (ha : d245546 p = 1) (hb : d310056 p = 1) : d310326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245541 q = 1) (hb : d310056 q = 1) : d310321 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245541, d310321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245541, d310321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80631 q ha hb
  have h2 (q : Pattern) (ha : d245542 q = 1) (hb : d310056 q = 1) : d310322 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245542, d310322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245542, d310322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245543 q = 1) (hb : d310056 q = 1) : d310323 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245543, d310323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245543, d310323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245544 q = 1) (hb : d310056 q = 1) : d310324 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245544, d310324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245544, d310324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245545 q = 1) (hb : d310056 q = 1) : d310325 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245545, d310325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245545, d310325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245546 q = 1) (hb : d310056 q = 1) : d310326 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245546, d310326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245546, d310326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80633 (p : Pattern) (ha : d32146 p = 1) (hb : d310056 p = 1) : d281372 p = 1 := by
  have h0 (q : Pattern) (ha : d31738 q = 1) (hb : d310056 q = 1) : d31738 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31304 q = 1) (hb : d310056 q = 1) : d31304 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32141 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32141, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32142 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32143 q = 1) (hb : d310056 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31739 q = 1) (hb : d310056 q = 1) : d31739 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32144 q = 1) (hb : d310056 q = 1) : d281370 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32144, d281370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32144, d281370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32145 q = 1) (hb : d310056 q = 1) : d281371 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32145, d281371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32145, d281371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d32146 q = 1) (hb : d310056 q = 1) : d281372 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32146, d281372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32146, d281372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80634 (p : Pattern) (ha : d32160 p = 1) (hb : d310056 p = 1) : d281382 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d310056 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32141 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32142 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32143 q = 1) (hb : d310056 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31306 q = 1) (hb : d310056 q = 1) : d31306 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32151 q = 1) (hb : d310056 q = 1) : d281377 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32151, d281377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32151, d281377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32152 q = 1) (hb : d310056 q = 1) : d281378 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32152, d281378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32152, d281378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d32154 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76224 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32155 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h12 (q : Pattern) (ha : d32156 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25766 q = 1) (hb : d310056 q = 1) : d25766 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d32157 q = 1) (hb : d310056 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32158 q = 1) (hb : d310056 q = 1) : d281380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d32159 q = 1) (hb : d310056 q = 1) : d281381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h17 (q : Pattern) (ha : d32160 q = 1) (hb : d310056 q = 1) : d281382 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32160, d281382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32160, d281382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro80635 (p : Pattern) (ha : d32171 p = 1) (hb : d310056 p = 1) : d281388 p = 1 := by
  have h0 (q : Pattern) (ha : d32170 q = 1) (hb : d310056 q = 1) : d32170 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32154 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76224 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32155 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h5 (q : Pattern) (ha : d32156 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25766 q = 1) (hb : d310056 q = 1) : d25766 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32157 q = 1) (hb : d310056 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32158 q = 1) (hb : d310056 q = 1) : d281380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32159 q = 1) (hb : d310056 q = 1) : d281381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h11 (q : Pattern) (ha : d32171 q = 1) (hb : d310056 q = 1) : d281388 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32171, d281388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32171, d281388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80636 (p : Pattern) (ha : d32180 p = 1) (hb : d310056 p = 1) : d310330 p = 1 := by
  have h0 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32154 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76224 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32155 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h4 (q : Pattern) (ha : d32156 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25766 q = 1) (hb : d310056 q = 1) : d25766 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32157 q = 1) (hb : d310056 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25767 q = 1) (hb : d310056 q = 1) : d25767 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32176 q = 1) (hb : d310056 q = 1) : d281393 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32176, d281393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32176, d281393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32177 q = 1) (hb : d310056 q = 1) : d281394 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32177, d281394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32177, d281394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32179 q = 1) (hb : d310056 q = 1) : d32179 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32180 q = 1) (hb : d310056 q = 1) : d310330 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32180, d310330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32180, d310330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80637 (p : Pattern) (ha : d32186 p = 1) (hb : d310056 p = 1) : d310336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32147 q = 1) (hb : d310056 q = 1) : d281373 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32147, d281373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80633 q ha hb
    | true =>
      simp only [d32147, d281373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32148 q = 1) (hb : d310056 q = 1) : d281374 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32148, d281374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32148, d281374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32149 q = 1) (hb : d310056 q = 1) : d281375 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32149, d281375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32149, d281375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32150 q = 1) (hb : d310056 q = 1) : d281376 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32150, d281376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32150, d281376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32161 q = 1) (hb : d310056 q = 1) : d281383 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32161, d281383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80634 q ha hb
    | true =>
      simp only [d32161, d281383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32162 q = 1) (hb : d310056 q = 1) : d281384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32162, d281384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32162, d281384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32163 q = 1) (hb : d310056 q = 1) : d281385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32163, d281385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32163, d281385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32164 q = 1) (hb : d310056 q = 1) : d281386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32164, d281386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32164, d281386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32165 q = 1) (hb : d310056 q = 1) : d281387 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32165, d281387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32165, d281387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32172 q = 1) (hb : d310056 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80635 q ha hb
    | true =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32173 q = 1) (hb : d310056 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32174 q = 1) (hb : d310056 q = 1) : d281391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32174, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32174, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32175 q = 1) (hb : d310056 q = 1) : d281392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32175, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32175, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32181 q = 1) (hb : d310056 q = 1) : d310331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
    | true =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32182 q = 1) (hb : d310056 q = 1) : d310332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d32183 q = 1) (hb : d310056 q = 1) : d310333 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d310333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d310333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32184 q = 1) (hb : d310056 q = 1) : d310334 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d310334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32184, d310334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32185 q = 1) (hb : d310056 q = 1) : d310335 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32185, d310335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32185, d310335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32186 q = 1) (hb : d310056 q = 1) : d310336 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32186, d310336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32186, d310336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro80638 (p : Pattern) (ha : d32193 p = 1) (hb : d310056 p = 1) : d310340 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d310056 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32141 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32142 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32143 q = 1) (hb : d310056 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31306 q = 1) (hb : d310056 q = 1) : d31306 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32151 q = 1) (hb : d310056 q = 1) : d281377 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32151, d281377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32151, d281377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32152 q = 1) (hb : d310056 q = 1) : d281378 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32152, d281378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32152, d281378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d32154 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76224 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32155 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h12 (q : Pattern) (ha : d32156 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32188 q = 1) (hb : d310056 q = 1) : d32188 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d32189 q = 1) (hb : d310056 q = 1) : d310337 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32189, d310337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32189, d310337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32190 q = 1) (hb : d310056 q = 1) : d32190 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d32191 q = 1) (hb : d310056 q = 1) : d310338 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32191, d310338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32191, d310338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32192 q = 1) (hb : d310056 q = 1) : d310339 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32192, d310339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32192, d310339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h18 (q : Pattern) (ha : d32193 q = 1) (hb : d310056 q = 1) : d310340 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32193, d310340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32193, d310340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro80639 (p : Pattern) (ha : d32198 p = 1) (hb : d310056 p = 1) : d310345 p = 1 := by
  have h0 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32154 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76224 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32155 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h4 (q : Pattern) (ha : d32156 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32188 q = 1) (hb : d310056 q = 1) : d32188 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32189 q = 1) (hb : d310056 q = 1) : d310337 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32189, d310337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32189, d310337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32190 q = 1) (hb : d310056 q = 1) : d32190 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32191 q = 1) (hb : d310056 q = 1) : d310338 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32191, d310338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32191, d310338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32192 q = 1) (hb : d310056 q = 1) : d310339 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32192, d310339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32192, d310339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32179 q = 1) (hb : d310056 q = 1) : d32179 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32198 q = 1) (hb : d310056 q = 1) : d310345 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32198, d310345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32198, d310345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80640 (p : Pattern) (ha : d32205 p = 1) (hb : d310056 p = 1) : d310352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32194 q = 1) (hb : d310056 q = 1) : d310341 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d310341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80638 q ha hb
    | true =>
      simp only [d32194, d310341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32195 q = 1) (hb : d310056 q = 1) : d310342 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d310342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32195, d310342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32196 q = 1) (hb : d310056 q = 1) : d310343 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32196, d310343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32196, d310343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32197 q = 1) (hb : d310056 q = 1) : d310344 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32197, d310344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32197, d310344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32199 q = 1) (hb : d310056 q = 1) : d310346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
    | true =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32200 q = 1) (hb : d310056 q = 1) : d310347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32201 q = 1) (hb : d310056 q = 1) : d310348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d310348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d310348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32202 q = 1) (hb : d310056 q = 1) : d310349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d310349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32202, d310349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32203 q = 1) (hb : d310056 q = 1) : d310350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32203, d310350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32203, d310350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32181 q = 1) (hb : d310056 q = 1) : d310331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
    | true =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32182 q = 1) (hb : d310056 q = 1) : d310332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32183 q = 1) (hb : d310056 q = 1) : d310333 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d310333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d310333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32184 q = 1) (hb : d310056 q = 1) : d310334 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d310334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32184, d310334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32204 q = 1) (hb : d310056 q = 1) : d310351 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32204, d310351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32204, d310351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32205 q = 1) (hb : d310056 q = 1) : d310352 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32205, d310352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32205, d310352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80641 (p : Pattern) (ha : d32210 p = 1) (hb : d310056 p = 1) : d310357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32199 q = 1) (hb : d310056 q = 1) : d310346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
    | true =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32200 q = 1) (hb : d310056 q = 1) : d310347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32201 q = 1) (hb : d310056 q = 1) : d310348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d310348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d310348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32202 q = 1) (hb : d310056 q = 1) : d310349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d310349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32202, d310349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32209 q = 1) (hb : d310056 q = 1) : d310356 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32209, d310356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32209, d310356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15165 q = 1) (hb : d310056 q = 1) : d15165 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32210 q = 1) (hb : d310056 q = 1) : d310357 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32210, d310357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32210, d310357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro80642 (p : Pattern) (ha : d32217 p = 1) (hb : d310056 p = 1) : d310364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32206 q = 1) (hb : d310056 q = 1) : d310353 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32206, d310353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80637 q ha hb
    | true =>
      simp only [d32206, d310353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80640 q ha hb
  have h2 (q : Pattern) (ha : d32207 q = 1) (hb : d310056 q = 1) : d310354 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32207, d310354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32207, d310354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32208 q = 1) (hb : d310056 q = 1) : d310355 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32208, d310355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32208, d310355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32211 q = 1) (hb : d310056 q = 1) : d310358 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d310358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80640 q ha hb
    | true =>
      simp only [d32211, d310358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80641 q ha hb
  have h5 (q : Pattern) (ha : d32212 q = 1) (hb : d310056 q = 1) : d310359 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d310359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d310359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32213 q = 1) (hb : d310056 q = 1) : d310360 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d310360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d310360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32214 q = 1) (hb : d310056 q = 1) : d310361 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32214, d310361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32214, d310361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32215 q = 1) (hb : d310056 q = 1) : d310362 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32215, d310362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32215, d310362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32216 q = 1) (hb : d310056 q = 1) : d310363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32216, d310363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32216, d310363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32217 q = 1) (hb : d310056 q = 1) : d310364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32217, d310364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32217, d310364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro80643 (p : Pattern) (ha : d32221 p = 1) (hb : d310056 p = 1) : d310368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32211 q = 1) (hb : d310056 q = 1) : d310358 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d310358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80640 q ha hb
    | true =>
      simp only [d32211, d310358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80641 q ha hb
  have h2 (q : Pattern) (ha : d32212 q = 1) (hb : d310056 q = 1) : d310359 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d310359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d310359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32213 q = 1) (hb : d310056 q = 1) : d310360 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d310360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d310360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32215 q = 1) (hb : d310056 q = 1) : d310362 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32215, d310362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32215, d310362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32220 q = 1) (hb : d310056 q = 1) : d310367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32220, d310367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32220, d310367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32221 q = 1) (hb : d310056 q = 1) : d310368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32221, d310368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32221, d310368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80644 (p : Pattern) (ha : d32227 p = 1) (hb : d310056 p = 1) : d310374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d310056 q = 1) : d310365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80642 q ha hb
    | true =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d310056 q = 1) : d310366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d310056 q = 1) : d310371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d310056 q = 1) : d310372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d310372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d310372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32226 q = 1) (hb : d310056 q = 1) : d310373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32226, d310373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32226, d310373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32227 q = 1) (hb : d310056 q = 1) : d310374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32227, d310374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32227, d310374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80645 (p : Pattern) (ha : d32231 p = 1) (hb : d310056 p = 1) : d310378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d310056 q = 1) : d310375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d310056 q = 1) : d310376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d310376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d310376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32230 q = 1) (hb : d310056 q = 1) : d310377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32230, d310377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32230, d310377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32231 q = 1) (hb : d310056 q = 1) : d310378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32231, d310378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32231, d310378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80646 (p : Pattern) (ha : d32237 p = 1) (hb : d310056 p = 1) : d310384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d310056 q = 1) : d310379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80644 q ha hb
    | true =>
      simp only [d32232, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80645 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d310056 q = 1) : d310380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d310056 q = 1) : d310381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d310056 q = 1) : d310382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d310056 q = 1) : d310383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32237 q = 1) (hb : d310056 q = 1) : d310384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32237, d310384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32237, d310384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80647 (p : Pattern) (ha : d32240 p = 1) (hb : d310056 p = 1) : d310387 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d310056 q = 1) : d310365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80642 q ha hb
    | true =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d310056 q = 1) : d310366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d310056 q = 1) : d310371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d310056 q = 1) : d310372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d310372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d310372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32226 q = 1) (hb : d310056 q = 1) : d310373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32226, d310373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32226, d310373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32240 q = 1) (hb : d310056 q = 1) : d310387 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32240, d310387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32240, d310387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80648 (p : Pattern) (ha : d32241 p = 1) (hb : d310056 p = 1) : d310388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d310056 q = 1) : d310375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d310056 q = 1) : d310376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d310376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d310376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32230 q = 1) (hb : d310056 q = 1) : d310377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32230, d310377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32230, d310377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32241 q = 1) (hb : d310056 q = 1) : d310388 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32241, d310388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32241, d310388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80649 (p : Pattern) (ha : d32247 p = 1) (hb : d310056 p = 1) : d310394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d310056 q = 1) : d310379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80644 q ha hb
    | true =>
      simp only [d32232, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80645 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d310056 q = 1) : d310380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d310056 q = 1) : d310381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d310056 q = 1) : d310382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d310056 q = 1) : d310383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32242 q = 1) (hb : d310056 q = 1) : d310389 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32242, d310389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80647 q ha hb
    | true =>
      simp only [d32242, d310389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80648 q ha hb
  have h7 (q : Pattern) (ha : d32243 q = 1) (hb : d310056 q = 1) : d310390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32243, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32243, d310390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32244 q = 1) (hb : d310056 q = 1) : d310391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32244, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32244, d310391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32245 q = 1) (hb : d310056 q = 1) : d310392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32245, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32245, d310392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32246 q = 1) (hb : d310056 q = 1) : d310393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32246, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32246, d310393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32247 q = 1) (hb : d310056 q = 1) : d310394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32247, d310394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32247, d310394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80650 (p : Pattern) (ha : d32466 p = 1) (hb : d310056 p = 1) : d310492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d310056 q = 1) : d310379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80644 q ha hb
    | true =>
      simp only [d32232, d310379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80645 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d310056 q = 1) : d310380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d310380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d310056 q = 1) : d310381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d310381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d310056 q = 1) : d310382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d310382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d310056 q = 1) : d310383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d310383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32461 q = 1) (hb : d310056 q = 1) : d310487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32461, d310487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80645 q ha hb
    | true =>
      simp only [d32461, d310487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32462 q = 1) (hb : d310056 q = 1) : d310488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32462, d310488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32462, d310488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32463 q = 1) (hb : d310056 q = 1) : d310489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32463, d310489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32463, d310489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32464 q = 1) (hb : d310056 q = 1) : d310490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32464, d310490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32464, d310490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32465 q = 1) (hb : d310056 q = 1) : d310491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32465, d310491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32465, d310491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32466 q = 1) (hb : d310056 q = 1) : d310492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32466, d310492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32466, d310492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80651 (p : Pattern) (ha : d32472 p = 1) (hb : d310056 p = 1) : d310498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32461 q = 1) (hb : d310056 q = 1) : d310487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32461, d310487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80645 q ha hb
    | true =>
      simp only [d32461, d310487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32462 q = 1) (hb : d310056 q = 1) : d310488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32462, d310488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32462, d310488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32463 q = 1) (hb : d310056 q = 1) : d310489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32463, d310489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32463, d310489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32464 q = 1) (hb : d310056 q = 1) : d310490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32464, d310490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32464, d310490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32465 q = 1) (hb : d310056 q = 1) : d310491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32465, d310491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32465, d310491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32467 q = 1) (hb : d310056 q = 1) : d310493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32467, d310493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80648 q ha hb
    | true =>
      simp only [d32467, d310493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32468 q = 1) (hb : d310056 q = 1) : d310494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32468, d310494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32468, d310494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32469 q = 1) (hb : d310056 q = 1) : d310495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32469, d310495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32469, d310495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32470 q = 1) (hb : d310056 q = 1) : d310496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32470, d310496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32470, d310496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32471 q = 1) (hb : d310056 q = 1) : d310497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32471, d310497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32471, d310497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32472 q = 1) (hb : d310056 q = 1) : d310498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32472, d310498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32472, d310498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80652 (p : Pattern) (ha : d32481 p = 1) (hb : d310056 p = 1) : d310507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32467 q = 1) (hb : d310056 q = 1) : d310493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32467, d310493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80648 q ha hb
    | true =>
      simp only [d32467, d310493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32468 q = 1) (hb : d310056 q = 1) : d310494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32468, d310494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32468, d310494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32469 q = 1) (hb : d310056 q = 1) : d310495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32469, d310495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32469, d310495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32470 q = 1) (hb : d310056 q = 1) : d310496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32470, d310496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32470, d310496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32471 q = 1) (hb : d310056 q = 1) : d310497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32471, d310497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32471, d310497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32481 q = 1) (hb : d310056 q = 1) : d310507 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32481, d310507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32481, d310507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80653 (p : Pattern) (ha : d32540 p = 1) (hb : d310056 p = 1) : d310537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32531 q = 1) (hb : d310056 q = 1) : d310528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32531, d310528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32531, d310528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80638 q ha hb
  have h2 (q : Pattern) (ha : d32194 q = 1) (hb : d310056 q = 1) : d310341 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d310341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80638 q ha hb
    | true =>
      simp only [d32194, d310341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32532 q = 1) (hb : d310056 q = 1) : d310529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32532, d310529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32532, d310529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32195 q = 1) (hb : d310056 q = 1) : d310342 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d310342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32195, d310342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32533 q = 1) (hb : d310056 q = 1) : d310530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32533, d310530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32533, d310530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32534 q = 1) (hb : d310056 q = 1) : d310531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32534, d310531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32534, d310531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32535 q = 1) (hb : d310056 q = 1) : d310532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32535, d310532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32535, d310532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
  have h8 (q : Pattern) (ha : d32199 q = 1) (hb : d310056 q = 1) : d310346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
    | true =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32536 q = 1) (hb : d310056 q = 1) : d310533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32536, d310533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32536, d310533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32200 q = 1) (hb : d310056 q = 1) : d310347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32537 q = 1) (hb : d310056 q = 1) : d310534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32537, d310534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32537, d310534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32538 q = 1) (hb : d310056 q = 1) : d310535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32538, d310535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32538, d310535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32539 q = 1) (hb : d310056 q = 1) : d310536 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32539, d310536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32539, d310536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32511 q = 1) (hb : d310056 q = 1) : d310513 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32511, d310513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32511, d310513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
  have h15 (q : Pattern) (ha : d32181 q = 1) (hb : d310056 q = 1) : d310331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
    | true =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d32512 q = 1) (hb : d310056 q = 1) : d310514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32512, d310514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32512, d310514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32182 q = 1) (hb : d310056 q = 1) : d310332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32513 q = 1) (hb : d310056 q = 1) : d310515 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32513, d310515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32513, d310515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32514 q = 1) (hb : d310056 q = 1) : d310516 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32514, d310516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32514, d310516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d32525 q = 1) (hb : d310056 q = 1) : d310522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32525, d310522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32525, d310522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d32540 q = 1) (hb : d310056 q = 1) : d310537 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32540, d310537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32540, d310537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro80654 (p : Pattern) (ha : d32545 p = 1) (hb : d310056 p = 1) : d310542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32535 q = 1) (hb : d310056 q = 1) : d310532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32535, d310532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32535, d310532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
  have h2 (q : Pattern) (ha : d32199 q = 1) (hb : d310056 q = 1) : d310346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
    | true =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32536 q = 1) (hb : d310056 q = 1) : d310533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32536, d310533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32536, d310533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32200 q = 1) (hb : d310056 q = 1) : d310347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32537 q = 1) (hb : d310056 q = 1) : d310534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32537, d310534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32537, d310534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32538 q = 1) (hb : d310056 q = 1) : d310535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32538, d310535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32538, d310535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32544 q = 1) (hb : d310056 q = 1) : d310541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32544, d310541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32544, d310541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15416 q = 1) (hb : d310056 q = 1) : d15416 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32545 q = 1) (hb : d310056 q = 1) : d310542 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32545, d310542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32545, d310542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro80655 (p : Pattern) (ha : d32564 p = 1) (hb : d310056 p = 1) : d310561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32546 q = 1) (hb : d310056 q = 1) : d310543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32546, d310543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80653 q ha hb
    | true =>
      simp only [d32546, d310543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80654 q ha hb
  have h2 (q : Pattern) (ha : d32547 q = 1) (hb : d310056 q = 1) : d310544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32547, d310544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32547, d310544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32548 q = 1) (hb : d310056 q = 1) : d310545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32548, d310545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32548, d310545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32554 q = 1) (hb : d310056 q = 1) : d310551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32554, d310551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32554, d310551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32563 q = 1) (hb : d310056 q = 1) : d310560 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32563, d310560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32563, d310560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32564 q = 1) (hb : d310056 q = 1) : d310561 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32564, d310561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32564, d310561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80656 (p : Pattern) (ha : d32664 p = 1) (hb : d310056 p = 1) : d310604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32565 q = 1) (hb : d310056 q = 1) : d310562 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32565, d310562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80655 q ha hb
    | true =>
      simp only [d32565, d310562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32566 q = 1) (hb : d310056 q = 1) : d310563 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32566, d310563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32566, d310563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32661 q = 1) (hb : d310056 q = 1) : d310601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32661, d310601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32661, d310601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32662 q = 1) (hb : d310056 q = 1) : d310602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32662, d310602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32662, d310602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32663 q = 1) (hb : d310056 q = 1) : d310603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32663, d310603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32663, d310603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32664 q = 1) (hb : d310056 q = 1) : d310604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32664, d310604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32664, d310604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80657 (p : Pattern) (ha : d32670 p = 1) (hb : d310056 p = 1) : d310610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32665 q = 1) (hb : d310056 q = 1) : d310605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32665, d310605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80656 q ha hb
    | true =>
      simp only [d32665, d310605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32666 q = 1) (hb : d310056 q = 1) : d310606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32666, d310606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32666, d310606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32667 q = 1) (hb : d310056 q = 1) : d310607 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32667, d310607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32667, d310607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32668 q = 1) (hb : d310056 q = 1) : d310608 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32668, d310608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32668, d310608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32669 q = 1) (hb : d310056 q = 1) : d310609 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32669, d310609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32669, d310609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32670 q = 1) (hb : d310056 q = 1) : d310610 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32670, d310610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32670, d310610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80658 (p : Pattern) (ha : d32252 p = 1) (hb : d310056 p = 1) : d310399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d310056 q = 1) : d310365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80642 q ha hb
    | true =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d310056 q = 1) : d310366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d310056 q = 1) : d310371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d310056 q = 1) : d310372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d310372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d310372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32251 q = 1) (hb : d310056 q = 1) : d310398 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32251, d310398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32251, d310398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32252 q = 1) (hb : d310056 q = 1) : d310399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32252, d310399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32252, d310399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80659 (p : Pattern) (ha : d32254 p = 1) (hb : d310056 p = 1) : d310401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d310056 q = 1) : d310375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d310056 q = 1) : d310376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d310376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d310376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32253 q = 1) (hb : d310056 q = 1) : d310400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32253, d310400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32253, d310400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32254 q = 1) (hb : d310056 q = 1) : d310401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32254, d310401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32254, d310401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80660 (p : Pattern) (ha : d32261 p = 1) (hb : d310056 p = 1) : d310408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d310056 q = 1) : d310365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80642 q ha hb
    | true =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d310056 q = 1) : d310366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d310056 q = 1) : d310371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32259 q = 1) (hb : d310056 q = 1) : d310406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32259, d310406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32259, d310406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32260 q = 1) (hb : d310056 q = 1) : d310407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32260, d310407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32260, d310407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32261 q = 1) (hb : d310056 q = 1) : d310408 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32261, d310408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32261, d310408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80661 (p : Pattern) (ha : d32264 p = 1) (hb : d310056 p = 1) : d310411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d310056 q = 1) : d310375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32262 q = 1) (hb : d310056 q = 1) : d310409 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32262, d310409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32262, d310409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32263 q = 1) (hb : d310056 q = 1) : d310410 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32263, d310410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32263, d310410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32264 q = 1) (hb : d310056 q = 1) : d310411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32264, d310411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32264, d310411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80662 (p : Pattern) (ha : d32280 p = 1) (hb : d310056 p = 1) : d281480 p = 1 := by
  have h0 (q : Pattern) (ha : d32278 q = 1) (hb : d310056 q = 1) : d32278 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32277 q = 1) (hb : d310056 q = 1) : d32277 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32172 q = 1) (hb : d310056 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80635 q ha hb
    | true =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32173 q = 1) (hb : d310056 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d32174 q = 1) (hb : d310056 q = 1) : d281391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32174, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32174, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32175 q = 1) (hb : d310056 q = 1) : d281392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32175, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32175, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d32279 q = 1) (hb : d310056 q = 1) : d281479 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32279, d281479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32279, d281479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32280 q = 1) (hb : d310056 q = 1) : d281480 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32280, d281480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32280, d281480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80663 (p : Pattern) (ha : d32286 p = 1) (hb : d310056 p = 1) : d281388 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d310056 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32141 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32142 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32143 q = 1) (hb : d310056 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32284 q = 1) (hb : d310056 q = 1) : d32169 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32284, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32284, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d32285 q = 1) (hb : d310056 q = 1) : d32170 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32285, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32285, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d32154 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76224 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32155 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h11 (q : Pattern) (ha : d32156 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25766 q = 1) (hb : d310056 q = 1) : d25766 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d32157 q = 1) (hb : d310056 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32158 q = 1) (hb : d310056 q = 1) : d281380 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32158, d281380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d32159 q = 1) (hb : d310056 q = 1) : d281381 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32159, d281381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h16 (q : Pattern) (ha : d32286 q = 1) (hb : d310056 q = 1) : d281388 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32286, d281388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32286, d281388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro80664 (p : Pattern) (ha : d32292 p = 1) (hb : d310056 p = 1) : d310418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32287 q = 1) (hb : d310056 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32287, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80663 q ha hb
    | true =>
      simp only [d32287, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32288 q = 1) (hb : d310056 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32288, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32288, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32289 q = 1) (hb : d310056 q = 1) : d281391 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32289, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32289, d281391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32290 q = 1) (hb : d310056 q = 1) : d281392 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32290, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32290, d281392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32181 q = 1) (hb : d310056 q = 1) : d310331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
    | true =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32182 q = 1) (hb : d310056 q = 1) : d310332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32183 q = 1) (hb : d310056 q = 1) : d310333 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d310333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d310333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32184 q = 1) (hb : d310056 q = 1) : d310334 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d310334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32184, d310334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32291 q = 1) (hb : d310056 q = 1) : d310335 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32291, d310335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32291, d310335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32204 q = 1) (hb : d310056 q = 1) : d310351 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32204, d310351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32204, d310351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32292 q = 1) (hb : d310056 q = 1) : d310418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32292, d310418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32292, d310418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80665 (p : Pattern) (ha : d32298 p = 1) (hb : d310056 p = 1) : d310424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32281 q = 1) (hb : d310056 q = 1) : d310415 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32281, d310415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80662 q ha hb
    | true =>
      simp only [d32281, d310415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80637 q ha hb
  have h2 (q : Pattern) (ha : d32282 q = 1) (hb : d310056 q = 1) : d310416 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32282, d310416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32282, d310416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32283 q = 1) (hb : d310056 q = 1) : d310417 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32283, d310417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32283, d310417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32293 q = 1) (hb : d310056 q = 1) : d310419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32293, d310419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80637 q ha hb
    | true =>
      simp only [d32293, d310419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80664 q ha hb
  have h5 (q : Pattern) (ha : d32294 q = 1) (hb : d310056 q = 1) : d310420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32294, d310420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32294, d310420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32295 q = 1) (hb : d310056 q = 1) : d310421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32295, d310421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32295, d310421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32296 q = 1) (hb : d310056 q = 1) : d310422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32296, d310422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32296, d310422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32206 q = 1) (hb : d310056 q = 1) : d310353 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32206, d310353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80637 q ha hb
    | true =>
      simp only [d32206, d310353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80640 q ha hb
  have h9 (q : Pattern) (ha : d32207 q = 1) (hb : d310056 q = 1) : d310354 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32207, d310354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32207, d310354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32208 q = 1) (hb : d310056 q = 1) : d310355 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32208, d310355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32208, d310355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32211 q = 1) (hb : d310056 q = 1) : d310358 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d310358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80640 q ha hb
    | true =>
      simp only [d32211, d310358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80641 q ha hb
  have h12 (q : Pattern) (ha : d32212 q = 1) (hb : d310056 q = 1) : d310359 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d310359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d310359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32213 q = 1) (hb : d310056 q = 1) : d310360 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d310360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d310360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32214 q = 1) (hb : d310056 q = 1) : d310361 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32214, d310361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32214, d310361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32297 q = 1) (hb : d310056 q = 1) : d310423 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32297, d310423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32297, d310423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32298 q = 1) (hb : d310056 q = 1) : d310424 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32298, d310424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32298, d310424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro80666 (p : Pattern) (ha : d32304 p = 1) (hb : d310056 p = 1) : d310430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32299 q = 1) (hb : d310056 q = 1) : d310425 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32299, d310425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80665 q ha hb
    | true =>
      simp only [d32299, d310425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32300 q = 1) (hb : d310056 q = 1) : d310426 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32300, d310426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32300, d310426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32218 q = 1) (hb : d310056 q = 1) : d310365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80642 q ha hb
    | true =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32219 q = 1) (hb : d310056 q = 1) : d310366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32301 q = 1) (hb : d310056 q = 1) : d310427 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32301, d310427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32301, d310427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32302 q = 1) (hb : d310056 q = 1) : d310428 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32302, d310428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32302, d310428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32303 q = 1) (hb : d310056 q = 1) : d310429 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32303, d310429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32303, d310429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32304 q = 1) (hb : d310056 q = 1) : d310430 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32304, d310430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32304, d310430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80667 (p : Pattern) (ha : d32404 p = 1) (hb : d310056 p = 1) : d310433 p = 1 := by
  have h0 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32154 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76224 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32155 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h4 (q : Pattern) (ha : d32156 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25766 q = 1) (hb : d310056 q = 1) : d25766 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32157 q = 1) (hb : d310056 q = 1) : d281379 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32157, d281379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25767 q = 1) (hb : d310056 q = 1) : d25767 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32176 q = 1) (hb : d310056 q = 1) : d281393 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32176, d281393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32176, d281393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32177 q = 1) (hb : d310056 q = 1) : d281394 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32177, d281394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32177, d281394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5132 q = 1) (hb : d310056 q = 1) : d5132 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32404 q = 1) (hb : d310056 q = 1) : d310433 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32404, d310433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32404, d310433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80668 (p : Pattern) (ha : d32410 p = 1) (hb : d310056 p = 1) : d310439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32194 q = 1) (hb : d310056 q = 1) : d310341 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d310341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80638 q ha hb
    | true =>
      simp only [d32194, d310341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32195 q = 1) (hb : d310056 q = 1) : d310342 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d310342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32195, d310342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32196 q = 1) (hb : d310056 q = 1) : d310343 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32196, d310343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32196, d310343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32197 q = 1) (hb : d310056 q = 1) : d310344 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32197, d310344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32197, d310344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32199 q = 1) (hb : d310056 q = 1) : d310346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
    | true =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32200 q = 1) (hb : d310056 q = 1) : d310347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32201 q = 1) (hb : d310056 q = 1) : d310348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d310348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d310348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32202 q = 1) (hb : d310056 q = 1) : d310349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d310349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32202, d310349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32203 q = 1) (hb : d310056 q = 1) : d310350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32203, d310350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32203, d310350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32405 q = 1) (hb : d310056 q = 1) : d310434 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32405, d310434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80667 q ha hb
    | true =>
      simp only [d32405, d310434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32406 q = 1) (hb : d310056 q = 1) : d310435 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32406, d310435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32406, d310435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32407 q = 1) (hb : d310056 q = 1) : d310436 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32407, d310436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32407, d310436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32408 q = 1) (hb : d310056 q = 1) : d310437 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32408, d310437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32408, d310437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32409 q = 1) (hb : d310056 q = 1) : d310438 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32409, d310438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32409, d310438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32410 q = 1) (hb : d310056 q = 1) : d310439 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32410, d310439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32410, d310439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80669 (p : Pattern) (ha : d32411 p = 1) (hb : d310056 p = 1) : d310440 p = 1 := by
  have h0 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32154 q = 1) (hb : d310056 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32154, d310056, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76224 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32155 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32155, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76158 q ha hb
  have h4 (q : Pattern) (ha : d32156 q = 1) (hb : d310056 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32156, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32188 q = 1) (hb : d310056 q = 1) : d32188 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32189 q = 1) (hb : d310056 q = 1) : d310337 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32189, d310337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32189, d310337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32190 q = 1) (hb : d310056 q = 1) : d32190 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32191 q = 1) (hb : d310056 q = 1) : d310338 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32191, d310338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32191, d310338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32192 q = 1) (hb : d310056 q = 1) : d310339 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32192, d310339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32192, d310339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5132 q = 1) (hb : d310056 q = 1) : d5132 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32411 q = 1) (hb : d310056 q = 1) : d310440 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32411, d310440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32411, d310440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80670 (p : Pattern) (ha : d32417 p = 1) (hb : d310056 p = 1) : d310446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32412 q = 1) (hb : d310056 q = 1) : d310441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32412, d310441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80669 q ha hb
    | true =>
      simp only [d32412, d310441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32413 q = 1) (hb : d310056 q = 1) : d310442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32413, d310442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32413, d310442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32414 q = 1) (hb : d310056 q = 1) : d310443 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32414, d310443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32414, d310443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32415 q = 1) (hb : d310056 q = 1) : d310444 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32415, d310444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32415, d310444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32416 q = 1) (hb : d310056 q = 1) : d310445 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32416, d310445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32416, d310445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32417 q = 1) (hb : d310056 q = 1) : d310446 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32417, d310446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32417, d310446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80671 (p : Pattern) (ha : d32423 p = 1) (hb : d310056 p = 1) : d310452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32206 q = 1) (hb : d310056 q = 1) : d310353 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32206, d310353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80637 q ha hb
    | true =>
      simp only [d32206, d310353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80640 q ha hb
  have h2 (q : Pattern) (ha : d32207 q = 1) (hb : d310056 q = 1) : d310354 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32207, d310354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32207, d310354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32208 q = 1) (hb : d310056 q = 1) : d310355 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32208, d310355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32208, d310355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32211 q = 1) (hb : d310056 q = 1) : d310358 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d310358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80640 q ha hb
    | true =>
      simp only [d32211, d310358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80641 q ha hb
  have h5 (q : Pattern) (ha : d32212 q = 1) (hb : d310056 q = 1) : d310359 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d310359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d310359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32213 q = 1) (hb : d310056 q = 1) : d310360 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d310360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d310360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32214 q = 1) (hb : d310056 q = 1) : d310361 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32214, d310361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32214, d310361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32418 q = 1) (hb : d310056 q = 1) : d310447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32418, d310447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80668 q ha hb
    | true =>
      simp only [d32418, d310447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80670 q ha hb
  have h9 (q : Pattern) (ha : d32419 q = 1) (hb : d310056 q = 1) : d310448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32419, d310448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32419, d310448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32420 q = 1) (hb : d310056 q = 1) : d310449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32420, d310449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32420, d310449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32421 q = 1) (hb : d310056 q = 1) : d310450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32421, d310450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32421, d310450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32422 q = 1) (hb : d310056 q = 1) : d310451 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32422, d310451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32422, d310451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32423 q = 1) (hb : d310056 q = 1) : d310452 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32423, d310452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32423, d310452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro80672 (p : Pattern) (ha : d32429 p = 1) (hb : d310056 p = 1) : d310458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32424 q = 1) (hb : d310056 q = 1) : d310453 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32424, d310453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80671 q ha hb
    | true =>
      simp only [d32424, d310453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32425 q = 1) (hb : d310056 q = 1) : d310454 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32425, d310454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32425, d310454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32426 q = 1) (hb : d310056 q = 1) : d310455 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32426, d310455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32426, d310455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32427 q = 1) (hb : d310056 q = 1) : d310456 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32427, d310456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32427, d310456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32428 q = 1) (hb : d310056 q = 1) : d310457 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32428, d310457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32428, d310457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32429 q = 1) (hb : d310056 q = 1) : d310458 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32429, d310458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32429, d310458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80673 (p : Pattern) (ha : d245554 p = 1) (hb : d310056 p = 1) : d310464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32255 q = 1) (hb : d310056 q = 1) : d310402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32255, d310402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80658 q ha hb
    | true =>
      simp only [d32255, d310402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80659 q ha hb
  have h2 (q : Pattern) (ha : d32256 q = 1) (hb : d310056 q = 1) : d310403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32256, d310403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32256, d310403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32257 q = 1) (hb : d310056 q = 1) : d310404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32257, d310404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32257, d310404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32258 q = 1) (hb : d310056 q = 1) : d310405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32258, d310405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32258, d310405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32265 q = 1) (hb : d310056 q = 1) : d310412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32265, d310412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80660 q ha hb
    | true =>
      simp only [d32265, d310412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80661 q ha hb
  have h6 (q : Pattern) (ha : d32266 q = 1) (hb : d310056 q = 1) : d310413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32266, d310413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32266, d310413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32267 q = 1) (hb : d310056 q = 1) : d310414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32267, d310414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32267, d310414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32305 q = 1) (hb : d310056 q = 1) : d310431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32305, d310431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80666 q ha hb
    | true =>
      simp only [d32305, d310431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80644 q ha hb
  have h9 (q : Pattern) (ha : d245550 q = 1) (hb : d310056 q = 1) : d310432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d310432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245550, d310432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d32430 q = 1) (hb : d310056 q = 1) : d310459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32430, d310459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80672 q ha hb
    | true =>
      simp only [d32430, d310459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32431 q = 1) (hb : d310056 q = 1) : d310460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32431, d310460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32431, d310460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245551 q = 1) (hb : d310056 q = 1) : d310461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d310461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245551, d310461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245552 q = 1) (hb : d310056 q = 1) : d310462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d310462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245552, d310462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245553 q = 1) (hb : d310056 q = 1) : d310463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d310463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245553, d310463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245554 q = 1) (hb : d310056 q = 1) : d310464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245554, d310464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245554, d310464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80674 (p : Pattern) (ha : d32436 p = 1) (hb : d310056 p = 1) : d310465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d310056 q = 1) : d310365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80642 q ha hb
    | true =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d310056 q = 1) : d310366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d310056 q = 1) : d310371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d310056 q = 1) : d310372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d310372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d310372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32251 q = 1) (hb : d310056 q = 1) : d310398 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32251, d310398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32251, d310398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32436 q = 1) (hb : d310056 q = 1) : d310465 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32436, d310465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32436, d310465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80675 (p : Pattern) (ha : d32437 p = 1) (hb : d310056 p = 1) : d310466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d310056 q = 1) : d310375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d310056 q = 1) : d310376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d310376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d310376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32253 q = 1) (hb : d310056 q = 1) : d310400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32253, d310400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32253, d310400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32437 q = 1) (hb : d310056 q = 1) : d310466 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32437, d310466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32437, d310466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80676 (p : Pattern) (ha : d32442 p = 1) (hb : d310056 p = 1) : d310471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d310056 q = 1) : d310365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80642 q ha hb
    | true =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d310056 q = 1) : d310366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d310056 q = 1) : d310371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d310371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32259 q = 1) (hb : d310056 q = 1) : d310406 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32259, d310406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32259, d310406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32260 q = 1) (hb : d310056 q = 1) : d310407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32260, d310407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32260, d310407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32442 q = 1) (hb : d310056 q = 1) : d310471 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32442, d310471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32442, d310471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80677 (p : Pattern) (ha : d32443 p = 1) (hb : d310056 p = 1) : d310472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d310056 q = 1) : d310369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80643 q ha hb
    | true =>
      simp only [d32222, d310369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d310056 q = 1) : d310370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d310370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d310056 q = 1) : d310375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d310375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32262 q = 1) (hb : d310056 q = 1) : d310409 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32262, d310409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32262, d310409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32263 q = 1) (hb : d310056 q = 1) : d310410 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32263, d310410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32263, d310410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32443 q = 1) (hb : d310056 q = 1) : d310472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32443, d310472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32443, d310472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80678 (p : Pattern) (ha : d32447 p = 1) (hb : d310056 p = 1) : d310476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32299 q = 1) (hb : d310056 q = 1) : d310425 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32299, d310425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80665 q ha hb
    | true =>
      simp only [d32299, d310425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32300 q = 1) (hb : d310056 q = 1) : d310426 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32300, d310426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32300, d310426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32218 q = 1) (hb : d310056 q = 1) : d310365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80642 q ha hb
    | true =>
      simp only [d32218, d310365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32219 q = 1) (hb : d310056 q = 1) : d310366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d310366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32301 q = 1) (hb : d310056 q = 1) : d310427 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32301, d310427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32301, d310427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32302 q = 1) (hb : d310056 q = 1) : d310428 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32302, d310428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32302, d310428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32303 q = 1) (hb : d310056 q = 1) : d310429 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32303, d310429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32303, d310429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32447 q = 1) (hb : d310056 q = 1) : d310476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32447, d310476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32447, d310476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80679 (p : Pattern) (ha : d32453 p = 1) (hb : d310056 p = 1) : d310479 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32424 q = 1) (hb : d310056 q = 1) : d310453 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32424, d310453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80671 q ha hb
    | true =>
      simp only [d32424, d310453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32425 q = 1) (hb : d310056 q = 1) : d310454 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32425, d310454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32425, d310454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32426 q = 1) (hb : d310056 q = 1) : d310455 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32426, d310455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32426, d310455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32427 q = 1) (hb : d310056 q = 1) : d310456 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32427, d310456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32427, d310456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32428 q = 1) (hb : d310056 q = 1) : d310457 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32428, d310457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32428, d310457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32453 q = 1) (hb : d310056 q = 1) : d310479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32453, d310479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32453, d310479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80680 (p : Pattern) (ha : d245559 p = 1) (hb : d310056 p = 1) : d310485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32255 q = 1) (hb : d310056 q = 1) : d310402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32255, d310402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80658 q ha hb
    | true =>
      simp only [d32255, d310402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80659 q ha hb
  have h2 (q : Pattern) (ha : d32256 q = 1) (hb : d310056 q = 1) : d310403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32256, d310403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32256, d310403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32257 q = 1) (hb : d310056 q = 1) : d310404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32257, d310404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32257, d310404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32258 q = 1) (hb : d310056 q = 1) : d310405 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32258, d310405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32258, d310405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32265 q = 1) (hb : d310056 q = 1) : d310412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32265, d310412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80660 q ha hb
    | true =>
      simp only [d32265, d310412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80661 q ha hb
  have h6 (q : Pattern) (ha : d32266 q = 1) (hb : d310056 q = 1) : d310413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32266, d310413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32266, d310413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32267 q = 1) (hb : d310056 q = 1) : d310414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32267, d310414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32267, d310414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32305 q = 1) (hb : d310056 q = 1) : d310431 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32305, d310431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80666 q ha hb
    | true =>
      simp only [d32305, d310431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80644 q ha hb
  have h9 (q : Pattern) (ha : d245550 q = 1) (hb : d310056 q = 1) : d310432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245550, d310432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245550, d310432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d32430 q = 1) (hb : d310056 q = 1) : d310459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32430, d310459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80672 q ha hb
    | true =>
      simp only [d32430, d310459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32431 q = 1) (hb : d310056 q = 1) : d310460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32431, d310460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32431, d310460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245551 q = 1) (hb : d310056 q = 1) : d310461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245551, d310461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245551, d310461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245552 q = 1) (hb : d310056 q = 1) : d310462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245552, d310462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245552, d310462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245553 q = 1) (hb : d310056 q = 1) : d310463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245553, d310463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245553, d310463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32438 q = 1) (hb : d310056 q = 1) : d310467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32438, d310467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80674 q ha hb
    | true =>
      simp only [d32438, d310467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80675 q ha hb
  have h16 (q : Pattern) (ha : d32439 q = 1) (hb : d310056 q = 1) : d310468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32439, d310468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32439, d310468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32440 q = 1) (hb : d310056 q = 1) : d310469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32440, d310469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32440, d310469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32441 q = 1) (hb : d310056 q = 1) : d310470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32441, d310470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32441, d310470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32444 q = 1) (hb : d310056 q = 1) : d310473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32444, d310473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80676 q ha hb
    | true =>
      simp only [d32444, d310473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80677 q ha hb
  have h20 (q : Pattern) (ha : d32445 q = 1) (hb : d310056 q = 1) : d310474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32445, d310474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32445, d310474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d32446 q = 1) (hb : d310056 q = 1) : d310475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32446, d310475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d32446, d310475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d32448 q = 1) (hb : d310056 q = 1) : d310477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32448, d310477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80678 q ha hb
    | true =>
      simp only [d32448, d310477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80647 q ha hb
  have h23 (q : Pattern) (ha : d245555 q = 1) (hb : d310056 q = 1) : d310478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d310478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245555, d310478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d32454 q = 1) (hb : d310056 q = 1) : d310480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32454, d310480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80679 q ha hb
    | true =>
      simp only [d32454, d310480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d32455 q = 1) (hb : d310056 q = 1) : d310481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32455, d310481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d32455, d310481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d245556 q = 1) (hb : d310056 q = 1) : d310482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d310482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245556, d310482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d245557 q = 1) (hb : d310056 q = 1) : d310483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245557, d310483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245557, d310483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d245558 q = 1) (hb : d310056 q = 1) : d310484 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245558, d310484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245558, d310484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d245559 q = 1) (hb : d310056 q = 1) : d310485 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245559, d310485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245559, d310485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro80681 (p : Pattern) (ha : d245566 p = 1) (hb : d310056 p = 1) : d310505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32448 q = 1) (hb : d310056 q = 1) : d310477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32448, d310477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80678 q ha hb
    | true =>
      simp only [d32448, d310477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80647 q ha hb
  have h2 (q : Pattern) (ha : d245555 q = 1) (hb : d310056 q = 1) : d310478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245555, d310478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245555, d310478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32454 q = 1) (hb : d310056 q = 1) : d310480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32454, d310480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80679 q ha hb
    | true =>
      simp only [d32454, d310480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32455 q = 1) (hb : d310056 q = 1) : d310481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32455, d310481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32455, d310481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245556 q = 1) (hb : d310056 q = 1) : d310482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245556, d310482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245556, d310482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245564 q = 1) (hb : d310056 q = 1) : d310503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245564, d310503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245564, d310503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245565 q = 1) (hb : d310056 q = 1) : d310504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245565, d310504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245565, d310504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245566 q = 1) (hb : d310056 q = 1) : d310505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245566, d310505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245566, d310505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80682 (p : Pattern) (ha : d32501 p = 1) (hb : d310056 p = 1) : d281584 p = 1 := by
  have h0 (q : Pattern) (ha : d32495 q = 1) (hb : d310056 q = 1) : d32495 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32494 q = 1) (hb : d310056 q = 1) : d32494 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32496 q = 1) (hb : d310056 q = 1) : d281579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32496, d281579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32496, d281579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80635 q ha hb
  have h4 (q : Pattern) (ha : d32172 q = 1) (hb : d310056 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80635 q ha hb
    | true =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d32497 q = 1) (hb : d310056 q = 1) : d281580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32497, d281580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32497, d281580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32173 q = 1) (hb : d310056 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d32498 q = 1) (hb : d310056 q = 1) : d281581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32498, d281581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32498, d281581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32499 q = 1) (hb : d310056 q = 1) : d281582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32499, d281582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32499, d281582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d32500 q = 1) (hb : d310056 q = 1) : d281583 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32500, d281583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32500, d281583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32501 q = 1) (hb : d310056 q = 1) : d281584 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32501, d281584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32501, d281584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80683 (p : Pattern) (ha : d32516 p = 1) (hb : d310056 p = 1) : d310518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32502 q = 1) (hb : d310056 q = 1) : d281585 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32502, d281585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32502, d281585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80633 q ha hb
  have h2 (q : Pattern) (ha : d32147 q = 1) (hb : d310056 q = 1) : d281373 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32147, d281373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80633 q ha hb
    | true =>
      simp only [d32147, d281373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32503 q = 1) (hb : d310056 q = 1) : d281586 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32503, d281586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32503, d281586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32148 q = 1) (hb : d310056 q = 1) : d281374 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32148, d281374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32148, d281374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32504 q = 1) (hb : d310056 q = 1) : d281587 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32504, d281587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32504, d281587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32505 q = 1) (hb : d310056 q = 1) : d281588 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32505, d281588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32505, d281588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32506 q = 1) (hb : d310056 q = 1) : d281589 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32506, d281589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32506, d281589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80634 q ha hb
  have h8 (q : Pattern) (ha : d32161 q = 1) (hb : d310056 q = 1) : d281383 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32161, d281383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80634 q ha hb
    | true =>
      simp only [d32161, d281383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32507 q = 1) (hb : d310056 q = 1) : d281590 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32507, d281590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32507, d281590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32162 q = 1) (hb : d310056 q = 1) : d281384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32162, d281384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32162, d281384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32508 q = 1) (hb : d310056 q = 1) : d281591 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32508, d281591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32508, d281591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32509 q = 1) (hb : d310056 q = 1) : d281592 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32509, d281592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32509, d281592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32510 q = 1) (hb : d310056 q = 1) : d281593 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32510, d281593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32510, d281593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32496 q = 1) (hb : d310056 q = 1) : d281579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32496, d281579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32496, d281579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80635 q ha hb
  have h15 (q : Pattern) (ha : d32172 q = 1) (hb : d310056 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80635 q ha hb
    | true =>
      simp only [d32172, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d32497 q = 1) (hb : d310056 q = 1) : d281580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32497, d281580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32497, d281580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32173 q = 1) (hb : d310056 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32173, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32498 q = 1) (hb : d310056 q = 1) : d281581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32498, d281581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32498, d281581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32499 q = 1) (hb : d310056 q = 1) : d281582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32499, d281582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32499, d281582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d32511 q = 1) (hb : d310056 q = 1) : d310513 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32511, d310513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32511, d310513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
  have h21 (q : Pattern) (ha : d32181 q = 1) (hb : d310056 q = 1) : d310331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
    | true =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d32512 q = 1) (hb : d310056 q = 1) : d310514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32512, d310514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d32512, d310514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d32182 q = 1) (hb : d310056 q = 1) : d310332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d32513 q = 1) (hb : d310056 q = 1) : d310515 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32513, d310515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d32513, d310515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d32514 q = 1) (hb : d310056 q = 1) : d310516 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32514, d310516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d32514, d310516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d32515 q = 1) (hb : d310056 q = 1) : d310517 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32515, d310517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32515, d310517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d32516 q = 1) (hb : d310056 q = 1) : d310518 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32516, d310518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32516, d310518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro80684 (p : Pattern) (ha : d32526 p = 1) (hb : d310056 p = 1) : d310523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32520 q = 1) (hb : d310056 q = 1) : d281579 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32520, d281579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32520, d281579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80663 q ha hb
  have h2 (q : Pattern) (ha : d32287 q = 1) (hb : d310056 q = 1) : d281389 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32287, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80663 q ha hb
    | true =>
      simp only [d32287, d281389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32521 q = 1) (hb : d310056 q = 1) : d281580 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32521, d281580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32521, d281580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32288 q = 1) (hb : d310056 q = 1) : d281390 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32288, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32288, d281390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32522 q = 1) (hb : d310056 q = 1) : d281581 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32522, d281581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32522, d281581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32523 q = 1) (hb : d310056 q = 1) : d281582 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32523, d281582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32523, d281582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32511 q = 1) (hb : d310056 q = 1) : d310513 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32511, d310513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32511, d310513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
  have h8 (q : Pattern) (ha : d32181 q = 1) (hb : d310056 q = 1) : d310331 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80636 q ha hb
    | true =>
      simp only [d32181, d310331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32512 q = 1) (hb : d310056 q = 1) : d310514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32512, d310514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32512, d310514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32182 q = 1) (hb : d310056 q = 1) : d310332 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32182, d310332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32513 q = 1) (hb : d310056 q = 1) : d310515 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32513, d310515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32513, d310515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32514 q = 1) (hb : d310056 q = 1) : d310516 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32514, d310516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32514, d310516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32524 q = 1) (hb : d310056 q = 1) : d310517 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32524, d310517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32524, d310517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32525 q = 1) (hb : d310056 q = 1) : d310522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32525, d310522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32525, d310522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32526 q = 1) (hb : d310056 q = 1) : d310523 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32526, d310523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32526, d310523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80685 (p : Pattern) (ha : d32551 p = 1) (hb : d310056 p = 1) : d310548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32517 q = 1) (hb : d310056 q = 1) : d310519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32517, d310519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80682 q ha hb
    | true =>
      simp only [d32517, d310519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80683 q ha hb
  have h2 (q : Pattern) (ha : d32518 q = 1) (hb : d310056 q = 1) : d310520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32518, d310520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32518, d310520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32519 q = 1) (hb : d310056 q = 1) : d310521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32519, d310521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32519, d310521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32527 q = 1) (hb : d310056 q = 1) : d310524 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32527, d310524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80683 q ha hb
    | true =>
      simp only [d32527, d310524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80684 q ha hb
  have h5 (q : Pattern) (ha : d32528 q = 1) (hb : d310056 q = 1) : d310525 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32528, d310525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32528, d310525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32529 q = 1) (hb : d310056 q = 1) : d310526 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32529, d310526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32529, d310526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32530 q = 1) (hb : d310056 q = 1) : d310527 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32530, d310527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32530, d310527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32541 q = 1) (hb : d310056 q = 1) : d310538 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32541, d310538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80683 q ha hb
    | true =>
      simp only [d32541, d310538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80653 q ha hb
  have h9 (q : Pattern) (ha : d32542 q = 1) (hb : d310056 q = 1) : d310539 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32542, d310539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32542, d310539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32543 q = 1) (hb : d310056 q = 1) : d310540 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32543, d310540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32543, d310540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32546 q = 1) (hb : d310056 q = 1) : d310543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32546, d310543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80653 q ha hb
    | true =>
      simp only [d32546, d310543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80654 q ha hb
  have h12 (q : Pattern) (ha : d32547 q = 1) (hb : d310056 q = 1) : d310544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32547, d310544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32547, d310544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32548 q = 1) (hb : d310056 q = 1) : d310545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32548, d310545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32548, d310545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32549 q = 1) (hb : d310056 q = 1) : d310546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32549, d310546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32549, d310546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32550 q = 1) (hb : d310056 q = 1) : d310547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32550, d310547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32550, d310547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32551 q = 1) (hb : d310056 q = 1) : d310548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32551, d310548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32551, d310548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro80686 (p : Pattern) (ha : d32556 p = 1) (hb : d310056 p = 1) : d310553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32541 q = 1) (hb : d310056 q = 1) : d310538 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32541, d310538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80683 q ha hb
    | true =>
      simp only [d32541, d310538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80653 q ha hb
  have h2 (q : Pattern) (ha : d32542 q = 1) (hb : d310056 q = 1) : d310539 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32542, d310539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32542, d310539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32543 q = 1) (hb : d310056 q = 1) : d310540 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32543, d310540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32543, d310540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32546 q = 1) (hb : d310056 q = 1) : d310543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32546, d310543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80653 q ha hb
    | true =>
      simp only [d32546, d310543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80654 q ha hb
  have h5 (q : Pattern) (ha : d32547 q = 1) (hb : d310056 q = 1) : d310544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32547, d310544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32547, d310544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32548 q = 1) (hb : d310056 q = 1) : d310545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32548, d310545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32548, d310545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32549 q = 1) (hb : d310056 q = 1) : d310546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32549, d310546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32549, d310546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32554 q = 1) (hb : d310056 q = 1) : d310551 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32554, d310551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32554, d310551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32555 q = 1) (hb : d310056 q = 1) : d310552 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32555, d310552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32555, d310552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32556 q = 1) (hb : d310056 q = 1) : d310553 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32556, d310553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32556, d310553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro80687 (p : Pattern) (ha : d32562 p = 1) (hb : d310056 p = 1) : d310559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32552 q = 1) (hb : d310056 q = 1) : d310549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32552, d310549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80685 q ha hb
    | true =>
      simp only [d32552, d310549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32553 q = 1) (hb : d310056 q = 1) : d310550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32553, d310550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32553, d310550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32557 q = 1) (hb : d310056 q = 1) : d310554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32557, d310554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80686 q ha hb
    | true =>
      simp only [d32557, d310554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32558 q = 1) (hb : d310056 q = 1) : d310555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32558, d310555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32558, d310555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32559 q = 1) (hb : d310056 q = 1) : d310556 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32559, d310556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32559, d310556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32560 q = 1) (hb : d310056 q = 1) : d310557 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32560, d310557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32560, d310557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32561 q = 1) (hb : d310056 q = 1) : d310558 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32561, d310558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32561, d310558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32562 q = 1) (hb : d310056 q = 1) : d310559 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32562, d310559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32562, d310559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80688 (p : Pattern) (ha : d32570 p = 1) (hb : d310056 p = 1) : d310567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32557 q = 1) (hb : d310056 q = 1) : d310554 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32557, d310554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80686 q ha hb
    | true =>
      simp only [d32557, d310554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32558 q = 1) (hb : d310056 q = 1) : d310555 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32558, d310555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32558, d310555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32565 q = 1) (hb : d310056 q = 1) : d310562 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32565, d310562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80655 q ha hb
    | true =>
      simp only [d32565, d310562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32566 q = 1) (hb : d310056 q = 1) : d310563 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32566, d310563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32566, d310563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32567 q = 1) (hb : d310056 q = 1) : d310564 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32567, d310564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32567, d310564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32568 q = 1) (hb : d310056 q = 1) : d310565 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32568, d310565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32568, d310565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32569 q = 1) (hb : d310056 q = 1) : d310566 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32569, d310566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32569, d310566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32570 q = 1) (hb : d310056 q = 1) : d310567 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32570, d310567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32570, d310567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80689 (p : Pattern) (ha : d32635 p = 1) (hb : d310056 p = 1) : d310575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32531 q = 1) (hb : d310056 q = 1) : d310528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32531, d310528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32531, d310528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80638 q ha hb
  have h2 (q : Pattern) (ha : d32194 q = 1) (hb : d310056 q = 1) : d310341 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d310341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80638 q ha hb
    | true =>
      simp only [d32194, d310341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32532 q = 1) (hb : d310056 q = 1) : d310529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32532, d310529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32532, d310529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32195 q = 1) (hb : d310056 q = 1) : d310342 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d310342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32195, d310342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32533 q = 1) (hb : d310056 q = 1) : d310530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32533, d310530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32533, d310530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32534 q = 1) (hb : d310056 q = 1) : d310531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32534, d310531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32534, d310531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32535 q = 1) (hb : d310056 q = 1) : d310532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32535, d310532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32535, d310532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
  have h8 (q : Pattern) (ha : d32199 q = 1) (hb : d310056 q = 1) : d310346 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80639 q ha hb
    | true =>
      simp only [d32199, d310346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32536 q = 1) (hb : d310056 q = 1) : d310533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32536, d310533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32536, d310533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32200 q = 1) (hb : d310056 q = 1) : d310347 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32200, d310347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32537 q = 1) (hb : d310056 q = 1) : d310534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32537, d310534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32537, d310534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32538 q = 1) (hb : d310056 q = 1) : d310535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32538, d310535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32538, d310535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32539 q = 1) (hb : d310056 q = 1) : d310536 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32539, d310536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32539, d310536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32630 q = 1) (hb : d310056 q = 1) : d310570 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32630, d310570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32630, d310570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80667 q ha hb
  have h15 (q : Pattern) (ha : d32405 q = 1) (hb : d310056 q = 1) : d310434 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32405, d310434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80667 q ha hb
    | true =>
      simp only [d32405, d310434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d32631 q = 1) (hb : d310056 q = 1) : d310571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32631, d310571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32631, d310571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32406 q = 1) (hb : d310056 q = 1) : d310435 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32406, d310435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32406, d310435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32632 q = 1) (hb : d310056 q = 1) : d310572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32632, d310572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32632, d310572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32633 q = 1) (hb : d310056 q = 1) : d310573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32633, d310573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32633, d310573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d32634 q = 1) (hb : d310056 q = 1) : d310574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32634, d310574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32634, d310574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d32635 q = 1) (hb : d310056 q = 1) : d310575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32635, d310575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32635, d310575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro80690 (p : Pattern) (ha : d32641 p = 1) (hb : d310056 p = 1) : d310581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32636 q = 1) (hb : d310056 q = 1) : d310576 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32636, d310576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32636, d310576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80669 q ha hb
  have h2 (q : Pattern) (ha : d32412 q = 1) (hb : d310056 q = 1) : d310441 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32412, d310441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80669 q ha hb
    | true =>
      simp only [d32412, d310441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32637 q = 1) (hb : d310056 q = 1) : d310577 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32637, d310577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32637, d310577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32413 q = 1) (hb : d310056 q = 1) : d310442 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32413, d310442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32413, d310442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32638 q = 1) (hb : d310056 q = 1) : d310578 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32638, d310578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32638, d310578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32639 q = 1) (hb : d310056 q = 1) : d310579 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32639, d310579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32639, d310579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32640 q = 1) (hb : d310056 q = 1) : d310580 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32640, d310580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32640, d310580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32641 q = 1) (hb : d310056 q = 1) : d310581 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32641, d310581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32641, d310581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80691 (p : Pattern) (ha : d32647 p = 1) (hb : d310056 p = 1) : d310587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32541 q = 1) (hb : d310056 q = 1) : d310538 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32541, d310538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80683 q ha hb
    | true =>
      simp only [d32541, d310538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80653 q ha hb
  have h2 (q : Pattern) (ha : d32542 q = 1) (hb : d310056 q = 1) : d310539 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32542, d310539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32542, d310539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32543 q = 1) (hb : d310056 q = 1) : d310540 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32543, d310540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32543, d310540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32546 q = 1) (hb : d310056 q = 1) : d310543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32546, d310543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80653 q ha hb
    | true =>
      simp only [d32546, d310543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80654 q ha hb
  have h5 (q : Pattern) (ha : d32547 q = 1) (hb : d310056 q = 1) : d310544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32547, d310544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32547, d310544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32548 q = 1) (hb : d310056 q = 1) : d310545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32548, d310545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32548, d310545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32549 q = 1) (hb : d310056 q = 1) : d310546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32549, d310546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32549, d310546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32642 q = 1) (hb : d310056 q = 1) : d310582 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32642, d310582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80689 q ha hb
    | true =>
      simp only [d32642, d310582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80690 q ha hb
  have h9 (q : Pattern) (ha : d32643 q = 1) (hb : d310056 q = 1) : d310583 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32643, d310583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32643, d310583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32644 q = 1) (hb : d310056 q = 1) : d310584 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32644, d310584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32644, d310584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32645 q = 1) (hb : d310056 q = 1) : d310585 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32645, d310585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32645, d310585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32646 q = 1) (hb : d310056 q = 1) : d310586 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32646, d310586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32646, d310586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32647 q = 1) (hb : d310056 q = 1) : d310587 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32647, d310587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32647, d310587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro80692 (p : Pattern) (ha : d32653 p = 1) (hb : d310056 p = 1) : d310593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32648 q = 1) (hb : d310056 q = 1) : d310588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32648, d310588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80691 q ha hb
    | true =>
      simp only [d32648, d310588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32649 q = 1) (hb : d310056 q = 1) : d310589 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32649, d310589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32649, d310589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32650 q = 1) (hb : d310056 q = 1) : d310590 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32650, d310590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32650, d310590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32651 q = 1) (hb : d310056 q = 1) : d310591 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32651, d310591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32651, d310591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32652 q = 1) (hb : d310056 q = 1) : d310592 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32652, d310592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32652, d310592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32653 q = 1) (hb : d310056 q = 1) : d310593 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32653, d310593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32653, d310593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80693 (p : Pattern) (ha : d245576 p = 1) (hb : d310056 p = 1) : d310599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32571 q = 1) (hb : d310056 q = 1) : d310568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32571, d310568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80687 q ha hb
    | true =>
      simp only [d32571, d310568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80688 q ha hb
  have h2 (q : Pattern) (ha : d245572 q = 1) (hb : d310056 q = 1) : d310569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245572, d310569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245572, d310569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32654 q = 1) (hb : d310056 q = 1) : d310594 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32654, d310594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80692 q ha hb
    | true =>
      simp only [d32654, d310594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32655 q = 1) (hb : d310056 q = 1) : d310595 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32655, d310595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32655, d310595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245573 q = 1) (hb : d310056 q = 1) : d310596 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245573, d310596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245573, d310596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245574 q = 1) (hb : d310056 q = 1) : d310597 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245574, d310597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245574, d310597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245575 q = 1) (hb : d310056 q = 1) : d310598 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245575, d310598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245575, d310598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245576 q = 1) (hb : d310056 q = 1) : d310599 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245576, d310599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245576, d310599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80694 (p : Pattern) (ha : d245582 p = 1) (hb : d310056 p = 1) : d310616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32238 q = 1) (hb : d310056 q = 1) : d310385 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32238, d310385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32238, d310385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80646 q ha hb
  have h2 (q : Pattern) (ha : d32239 q = 1) (hb : d310056 q = 1) : d310386 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32239, d310386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32239, d310386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32248 q = 1) (hb : d310056 q = 1) : d310395 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32248, d310395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80646 q ha hb
    | true =>
      simp only [d32248, d310395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80649 q ha hb
  have h4 (q : Pattern) (ha : d32249 q = 1) (hb : d310056 q = 1) : d310396 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d32249, d310396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32249, d310396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32250 q = 1) (hb : d310056 q = 1) : d310397 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d32250, d310397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32250, d310397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245560 q = 1) (hb : d310056 q = 1) : d310486 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245560, d310486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80673 q ha hb
    | true =>
      simp only [d245560, d310486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80680 q ha hb
  have h7 (q : Pattern) (ha : d32473 q = 1) (hb : d310056 q = 1) : d310499 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32473, d310499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80650 q ha hb
    | true =>
      simp only [d32473, d310499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80651 q ha hb
  have h8 (q : Pattern) (ha : d245561 q = 1) (hb : d310056 q = 1) : d310500 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245561, d310500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245561, d310500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d245562 q = 1) (hb : d310056 q = 1) : d310501 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245562, d310501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245562, d310501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d245563 q = 1) (hb : d310056 q = 1) : d310502 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245563, d310502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245563, d310502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d245567 q = 1) (hb : d310056 q = 1) : d310506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245567, d310506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245567, d310506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80681 q ha hb
  have h12 (q : Pattern) (ha : d32482 q = 1) (hb : d310056 q = 1) : d310508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32482, d310508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32482, d310508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80652 q ha hb
  have h13 (q : Pattern) (ha : d245568 q = 1) (hb : d310056 q = 1) : d310509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245568, d310509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245568, d310509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245569 q = 1) (hb : d310056 q = 1) : d310510 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245569, d310510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245569, d310510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d245570 q = 1) (hb : d310056 q = 1) : d310511 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245570, d310511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245570, d310511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d245571 q = 1) (hb : d310056 q = 1) : d310512 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245571, d310512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245571, d310512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d245577 q = 1) (hb : d310056 q = 1) : d310600 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245577, d310600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245577, d310600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80693 q ha hb
  have h18 (q : Pattern) (ha : d32671 q = 1) (hb : d310056 q = 1) : d310611 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32671, d310611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32671, d310611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80657 q ha hb
  have h19 (q : Pattern) (ha : d245578 q = 1) (hb : d310056 q = 1) : d310612 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245578, d310612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245578, d310612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d245579 q = 1) (hb : d310056 q = 1) : d310613 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245579, d310613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245579, d310613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d245580 q = 1) (hb : d310056 q = 1) : d310614 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245580, d310614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245580, d310614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d245581 q = 1) (hb : d310056 q = 1) : d310615 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245581, d310615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245581, d310615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d245582 q = 1) (hb : d310056 q = 1) : d310616 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245582, d310616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245582, d310616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro80695 (p : Pattern) (ha : d245588 p = 1) (hb : d310056 p = 1) : d310622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d245583 q = 1) (hb : d310056 q = 1) : d310617 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245583, d310617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245583, d310617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80694 q ha hb
  have h2 (q : Pattern) (ha : d245584 q = 1) (hb : d310056 q = 1) : d310618 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245584, d310618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245584, d310618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d245585 q = 1) (hb : d310056 q = 1) : d310619 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245585, d310619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245585, d310619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d245586 q = 1) (hb : d310056 q = 1) : d310620 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245586, d310620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245586, d310620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d245587 q = 1) (hb : d310056 q = 1) : d310621 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245587, d310621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245587, d310621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245588 q = 1) (hb : d310056 q = 1) : d310622 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245588, d310622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245588, d310622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80696 (p : Pattern) (ha : d32707 p = 1) (hb : d310056 p = 1) : d281711 p = 1 := by
  have h0 (q : Pattern) (ha : d32692 q = 1) (hb : d310056 q = 1) : d32692 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32687 q = 1) (hb : d202304 q = 1) : d32687 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32699 q = 1) (hb : d310056 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76289 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10055 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h5 (q : Pattern) (ha : d32700 q = 1) (hb : d310056 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32703 q = 1) (hb : d310056 q = 1) : d32703 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32704 q = 1) (hb : d310056 q = 1) : d281708 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32704, d281708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32704, d281708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32705 q = 1) (hb : d310056 q = 1) : d281709 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32705, d281709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32705, d281709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32706 q = 1) (hb : d310056 q = 1) : d281710 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32706, d281710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32706, d281710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h11 (q : Pattern) (ha : d32707 q = 1) (hb : d310056 q = 1) : d281711 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32707, d281711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32707, d281711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80697 (p : Pattern) (ha : d32715 p = 1) (hb : d310056 p = 1) : d297516 p = 1 := by
  have h0 (q : Pattern) (ha : d32687 q = 1) (hb : d202304 q = 1) : d32687 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32699 q = 1) (hb : d310056 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76289 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h4 (q : Pattern) (ha : d32700 q = 1) (hb : d310056 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32703 q = 1) (hb : d310056 q = 1) : d32703 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32704 q = 1) (hb : d310056 q = 1) : d281708 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32704, d281708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32704, d281708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32705 q = 1) (hb : d310056 q = 1) : d281709 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32705, d281709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32705, d281709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32706 q = 1) (hb : d310056 q = 1) : d281710 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32706, d281710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32706, d281710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d32714 q = 1) (hb : d310056 q = 1) : d32714 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32715 q = 1) (hb : d310056 q = 1) : d297516 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32715, d297516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32715, d297516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80698 (p : Pattern) (ha : d32721 p = 1) (hb : d310056 p = 1) : d297522 p = 1 := by
  have h0 (q : Pattern) (ha : d32697 q = 1) (hb : d310056 q = 1) : d32697 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32708 q = 1) (hb : d310056 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
    | true =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32709 q = 1) (hb : d310056 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d32710 q = 1) (hb : d310056 q = 1) : d281714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32710, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32711 q = 1) (hb : d310056 q = 1) : d281715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32711, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d32712 q = 1) (hb : d310056 q = 1) : d281716 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32712, d281716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32712, d281716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32716 q = 1) (hb : d310056 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
    | true =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d32717 q = 1) (hb : d310056 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d32718 q = 1) (hb : d310056 q = 1) : d297519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32718, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32718, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32719 q = 1) (hb : d310056 q = 1) : d297520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32719, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32719, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d32720 q = 1) (hb : d310056 q = 1) : d297521 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32720, d297521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32720, d297521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32721 q = 1) (hb : d310056 q = 1) : d297522 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32721, d297522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32721, d297522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80699 (p : Pattern) (ha : d32727 p = 1) (hb : d310056 p = 1) : d297526 p = 1 := by
  have h0 (q : Pattern) (ha : d32692 q = 1) (hb : d310056 q = 1) : d32692 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32687 q = 1) (hb : d202304 q = 1) : d32687 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32699 q = 1) (hb : d310056 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76289 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10055 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h5 (q : Pattern) (ha : d32700 q = 1) (hb : d310056 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32723 q = 1) (hb : d310056 q = 1) : d32723 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32724 q = 1) (hb : d310056 q = 1) : d297523 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32724, d297523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32724, d297523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30103 q = 1) (hb : d310056 q = 1) : d30103 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32725 q = 1) (hb : d310056 q = 1) : d297524 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32725, d297524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32725, d297524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32726 q = 1) (hb : d310056 q = 1) : d297525 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32726, d297525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32726, d297525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32727 q = 1) (hb : d310056 q = 1) : d297526 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32727, d297526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32727, d297526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80700 (p : Pattern) (ha : d32732 p = 1) (hb : d310056 p = 1) : d297531 p = 1 := by
  have h0 (q : Pattern) (ha : d32687 q = 1) (hb : d202304 q = 1) : d32687 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32699 q = 1) (hb : d310056 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76289 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h4 (q : Pattern) (ha : d32700 q = 1) (hb : d310056 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32723 q = 1) (hb : d310056 q = 1) : d32723 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32724 q = 1) (hb : d310056 q = 1) : d297523 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32724, d297523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32724, d297523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30103 q = 1) (hb : d310056 q = 1) : d30103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32725 q = 1) (hb : d310056 q = 1) : d297524 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32725, d297524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32725, d297524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32726 q = 1) (hb : d310056 q = 1) : d297525 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32726, d297525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32726, d297525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32714 q = 1) (hb : d310056 q = 1) : d32714 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32732 q = 1) (hb : d310056 q = 1) : d297531 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32732, d297531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32732, d297531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80701 (p : Pattern) (ha : d32739 p = 1) (hb : d310056 p = 1) : d297538 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32728 q = 1) (hb : d310056 q = 1) : d297527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32728, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80699 q ha hb
    | true =>
      simp only [d32728, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32729 q = 1) (hb : d310056 q = 1) : d297528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32729, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32729, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32730 q = 1) (hb : d310056 q = 1) : d297529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32730, d297529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32730, d297529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32731 q = 1) (hb : d310056 q = 1) : d297530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32731, d297530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32731, d297530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32733 q = 1) (hb : d310056 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
    | true =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32734 q = 1) (hb : d310056 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32735 q = 1) (hb : d310056 q = 1) : d297534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32735, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32735, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32736 q = 1) (hb : d310056 q = 1) : d297535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32736, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32736, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32737 q = 1) (hb : d310056 q = 1) : d297536 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32737, d297536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32737, d297536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32716 q = 1) (hb : d310056 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
    | true =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32717 q = 1) (hb : d310056 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32718 q = 1) (hb : d310056 q = 1) : d297519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32718, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32718, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32719 q = 1) (hb : d310056 q = 1) : d297520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32719, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32719, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32738 q = 1) (hb : d310056 q = 1) : d297537 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32738, d297537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32738, d297537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32739 q = 1) (hb : d310056 q = 1) : d297538 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32739, d297538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32739, d297538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80702 (p : Pattern) (ha : d32744 p = 1) (hb : d310056 p = 1) : d297543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32733 q = 1) (hb : d310056 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
    | true =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32734 q = 1) (hb : d310056 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32735 q = 1) (hb : d310056 q = 1) : d297534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32735, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32735, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32736 q = 1) (hb : d310056 q = 1) : d297535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32736, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32736, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32743 q = 1) (hb : d310056 q = 1) : d297542 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32743, d297542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32743, d297542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15557 q = 1) (hb : d310056 q = 1) : d15557 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32744 q = 1) (hb : d310056 q = 1) : d297543 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32744, d297543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32744, d297543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro80703 (p : Pattern) (ha : d32751 p = 1) (hb : d310056 p = 1) : d297550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32740 q = 1) (hb : d310056 q = 1) : d297539 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32740, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80698 q ha hb
    | true =>
      simp only [d32740, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80701 q ha hb
  have h2 (q : Pattern) (ha : d32741 q = 1) (hb : d310056 q = 1) : d297540 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32741, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32741, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32742 q = 1) (hb : d310056 q = 1) : d297541 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32742, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32742, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32745 q = 1) (hb : d310056 q = 1) : d297544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32745, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80701 q ha hb
    | true =>
      simp only [d32745, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80702 q ha hb
  have h5 (q : Pattern) (ha : d32746 q = 1) (hb : d310056 q = 1) : d297545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32746, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32746, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32747 q = 1) (hb : d310056 q = 1) : d297546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32747, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32747, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32748 q = 1) (hb : d310056 q = 1) : d297547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32748, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32748, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32749 q = 1) (hb : d310056 q = 1) : d297548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32749, d297548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32749, d297548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32750 q = 1) (hb : d310056 q = 1) : d297549 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32750, d297549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32750, d297549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32751 q = 1) (hb : d310056 q = 1) : d297550 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32751, d297550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32751, d297550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro80704 (p : Pattern) (ha : d32755 p = 1) (hb : d310056 p = 1) : d297554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32745 q = 1) (hb : d310056 q = 1) : d297544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32745, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80701 q ha hb
    | true =>
      simp only [d32745, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80702 q ha hb
  have h2 (q : Pattern) (ha : d32746 q = 1) (hb : d310056 q = 1) : d297545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32746, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32746, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32747 q = 1) (hb : d310056 q = 1) : d297546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32747, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32747, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32749 q = 1) (hb : d310056 q = 1) : d297548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32749, d297548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32749, d297548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32754 q = 1) (hb : d310056 q = 1) : d297553 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32754, d297553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32754, d297553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32755 q = 1) (hb : d310056 q = 1) : d297554 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32755, d297554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32755, d297554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80705 (p : Pattern) (ha : d32761 p = 1) (hb : d310056 p = 1) : d297560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32752 q = 1) (hb : d310056 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80703 q ha hb
    | true =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32753 q = 1) (hb : d310056 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32758 q = 1) (hb : d310056 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32759 q = 1) (hb : d310056 q = 1) : d297558 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32759, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32759, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32760 q = 1) (hb : d310056 q = 1) : d297559 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32760, d297559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32760, d297559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32761 q = 1) (hb : d310056 q = 1) : d297560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32761, d297560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32761, d297560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80706 (p : Pattern) (ha : d32765 p = 1) (hb : d310056 p = 1) : d297564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32762 q = 1) (hb : d310056 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32763 q = 1) (hb : d310056 q = 1) : d297562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32763, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32763, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32764 q = 1) (hb : d310056 q = 1) : d297563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32764, d297563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32764, d297563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32765 q = 1) (hb : d310056 q = 1) : d297564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32765, d297564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32765, d297564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80707 (p : Pattern) (ha : d32771 p = 1) (hb : d310056 p = 1) : d297570 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32766 q = 1) (hb : d310056 q = 1) : d297565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32766, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80705 q ha hb
    | true =>
      simp only [d32766, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80706 q ha hb
  have h2 (q : Pattern) (ha : d32767 q = 1) (hb : d310056 q = 1) : d297566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32767, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32767, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32768 q = 1) (hb : d310056 q = 1) : d297567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32768, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32768, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32769 q = 1) (hb : d310056 q = 1) : d297568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32769, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32769, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32770 q = 1) (hb : d310056 q = 1) : d297569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32770, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32770, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32771 q = 1) (hb : d310056 q = 1) : d297570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32771, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32771, d297570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80708 (p : Pattern) (ha : d32774 p = 1) (hb : d310056 p = 1) : d297573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32752 q = 1) (hb : d310056 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80703 q ha hb
    | true =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32753 q = 1) (hb : d310056 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32758 q = 1) (hb : d310056 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32759 q = 1) (hb : d310056 q = 1) : d297558 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32759, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32759, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32760 q = 1) (hb : d310056 q = 1) : d297559 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32760, d297559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32760, d297559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32774 q = 1) (hb : d310056 q = 1) : d297573 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32774, d297573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32774, d297573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80709 (p : Pattern) (ha : d32775 p = 1) (hb : d310056 p = 1) : d297574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32762 q = 1) (hb : d310056 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32763 q = 1) (hb : d310056 q = 1) : d297562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32763, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32763, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32764 q = 1) (hb : d310056 q = 1) : d297563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32764, d297563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32764, d297563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32775 q = 1) (hb : d310056 q = 1) : d297574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32775, d297574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32775, d297574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80710 (p : Pattern) (ha : d32781 p = 1) (hb : d310056 p = 1) : d297580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32766 q = 1) (hb : d310056 q = 1) : d297565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32766, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80705 q ha hb
    | true =>
      simp only [d32766, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80706 q ha hb
  have h2 (q : Pattern) (ha : d32767 q = 1) (hb : d310056 q = 1) : d297566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32767, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32767, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32768 q = 1) (hb : d310056 q = 1) : d297567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32768, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32768, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32769 q = 1) (hb : d310056 q = 1) : d297568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32769, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32769, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32770 q = 1) (hb : d310056 q = 1) : d297569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32770, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32770, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32776 q = 1) (hb : d310056 q = 1) : d297575 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32776, d297575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80708 q ha hb
    | true =>
      simp only [d32776, d297575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80709 q ha hb
  have h7 (q : Pattern) (ha : d32777 q = 1) (hb : d310056 q = 1) : d297576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32777, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32777, d297576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32778 q = 1) (hb : d310056 q = 1) : d297577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32778, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32778, d297577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32779 q = 1) (hb : d310056 q = 1) : d297578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32779, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32779, d297578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32780 q = 1) (hb : d310056 q = 1) : d297579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32780, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32780, d297579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32781 q = 1) (hb : d310056 q = 1) : d297580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32781, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32781, d297580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80711 (p : Pattern) (ha : d32970 p = 1) (hb : d310056 p = 1) : d297681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32766 q = 1) (hb : d310056 q = 1) : d297565 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32766, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80705 q ha hb
    | true =>
      simp only [d32766, d297565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80706 q ha hb
  have h2 (q : Pattern) (ha : d32767 q = 1) (hb : d310056 q = 1) : d297566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32767, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32767, d297566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32768 q = 1) (hb : d310056 q = 1) : d297567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32768, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32768, d297567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32769 q = 1) (hb : d310056 q = 1) : d297568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32769, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32769, d297568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32770 q = 1) (hb : d310056 q = 1) : d297569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32770, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32770, d297569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32965 q = 1) (hb : d310056 q = 1) : d297676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32965, d297676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80706 q ha hb
    | true =>
      simp only [d32965, d297676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32966 q = 1) (hb : d310056 q = 1) : d297677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32966, d297677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32966, d297677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32967 q = 1) (hb : d310056 q = 1) : d297678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32967, d297678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32967, d297678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32968 q = 1) (hb : d310056 q = 1) : d297679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32968, d297679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32968, d297679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32969 q = 1) (hb : d310056 q = 1) : d297680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32969, d297680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32969, d297680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32970 q = 1) (hb : d310056 q = 1) : d297681 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32970, d297681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32970, d297681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80712 (p : Pattern) (ha : d32976 p = 1) (hb : d310056 p = 1) : d297687 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32965 q = 1) (hb : d310056 q = 1) : d297676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32965, d297676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80706 q ha hb
    | true =>
      simp only [d32965, d297676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32966 q = 1) (hb : d310056 q = 1) : d297677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32966, d297677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32966, d297677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32967 q = 1) (hb : d310056 q = 1) : d297678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32967, d297678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32967, d297678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32968 q = 1) (hb : d310056 q = 1) : d297679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32968, d297679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32968, d297679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32969 q = 1) (hb : d310056 q = 1) : d297680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32969, d297680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32969, d297680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32971 q = 1) (hb : d310056 q = 1) : d297682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32971, d297682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80709 q ha hb
    | true =>
      simp only [d32971, d297682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32972 q = 1) (hb : d310056 q = 1) : d297683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32972, d297683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32972, d297683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32973 q = 1) (hb : d310056 q = 1) : d297684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32973, d297684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32973, d297684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32974 q = 1) (hb : d310056 q = 1) : d297685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32974, d297685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32974, d297685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32975 q = 1) (hb : d310056 q = 1) : d297686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32975, d297686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32975, d297686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32976 q = 1) (hb : d310056 q = 1) : d297687 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32976, d297687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32976, d297687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80713 (p : Pattern) (ha : d32985 p = 1) (hb : d310056 p = 1) : d297696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32971 q = 1) (hb : d310056 q = 1) : d297682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32971, d297682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80709 q ha hb
    | true =>
      simp only [d32971, d297682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32972 q = 1) (hb : d310056 q = 1) : d297683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32972, d297683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32972, d297683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32973 q = 1) (hb : d310056 q = 1) : d297684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32973, d297684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32973, d297684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32974 q = 1) (hb : d310056 q = 1) : d297685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32974, d297685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32974, d297685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32975 q = 1) (hb : d310056 q = 1) : d297686 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32975, d297686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32975, d297686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32985 q = 1) (hb : d310056 q = 1) : d297696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32985, d297696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32985, d297696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80714 (p : Pattern) (ha : d33026 p = 1) (hb : d310056 p = 1) : d297726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33017 q = 1) (hb : d310056 q = 1) : d297717 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33017, d297717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33017, d297717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80699 q ha hb
  have h2 (q : Pattern) (ha : d32728 q = 1) (hb : d310056 q = 1) : d297527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32728, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80699 q ha hb
    | true =>
      simp only [d32728, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33018 q = 1) (hb : d310056 q = 1) : d297718 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33018, d297718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33018, d297718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32729 q = 1) (hb : d310056 q = 1) : d297528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32729, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32729, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33019 q = 1) (hb : d310056 q = 1) : d297719 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33019, d297719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33019, d297719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33020 q = 1) (hb : d310056 q = 1) : d297720 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33020, d297720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33020, d297720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33021 q = 1) (hb : d310056 q = 1) : d297721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33021, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33021, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
  have h8 (q : Pattern) (ha : d32733 q = 1) (hb : d310056 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
    | true =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33022 q = 1) (hb : d310056 q = 1) : d297722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33022, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33022, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32734 q = 1) (hb : d310056 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33023 q = 1) (hb : d310056 q = 1) : d297723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33023, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33023, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33024 q = 1) (hb : d310056 q = 1) : d297724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33024, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33024, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33025 q = 1) (hb : d310056 q = 1) : d297725 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33025, d297725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33025, d297725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33002 q = 1) (hb : d310056 q = 1) : d297702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33002, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33002, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
  have h15 (q : Pattern) (ha : d32716 q = 1) (hb : d310056 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
    | true =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33003 q = 1) (hb : d310056 q = 1) : d297703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33003, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33003, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32717 q = 1) (hb : d310056 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33004 q = 1) (hb : d310056 q = 1) : d297704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33004, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33004, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33005 q = 1) (hb : d310056 q = 1) : d297705 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33005, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33005, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d33011 q = 1) (hb : d310056 q = 1) : d297711 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33011, d297711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33011, d297711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d33026 q = 1) (hb : d310056 q = 1) : d297726 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33026, d297726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33026, d297726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro80715 (p : Pattern) (ha : d33031 p = 1) (hb : d310056 p = 1) : d297731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33021 q = 1) (hb : d310056 q = 1) : d297721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33021, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33021, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
  have h2 (q : Pattern) (ha : d32733 q = 1) (hb : d310056 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
    | true =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33022 q = 1) (hb : d310056 q = 1) : d297722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33022, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33022, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32734 q = 1) (hb : d310056 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33023 q = 1) (hb : d310056 q = 1) : d297723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33023, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33023, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33024 q = 1) (hb : d310056 q = 1) : d297724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33024, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33024, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33030 q = 1) (hb : d310056 q = 1) : d297730 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33030, d297730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33030, d297730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15794 q = 1) (hb : d310056 q = 1) : d15794 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d33031 q = 1) (hb : d310056 q = 1) : d297731 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33031, d297731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33031, d297731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro80716 (p : Pattern) (ha : d33050 p = 1) (hb : d310056 p = 1) : d297750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33032 q = 1) (hb : d310056 q = 1) : d297732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33032, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80714 q ha hb
    | true =>
      simp only [d33032, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80715 q ha hb
  have h2 (q : Pattern) (ha : d33033 q = 1) (hb : d310056 q = 1) : d297733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33033, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33033, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33034 q = 1) (hb : d310056 q = 1) : d297734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33034, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33034, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33040 q = 1) (hb : d310056 q = 1) : d297740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33040, d297740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33040, d297740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33049 q = 1) (hb : d310056 q = 1) : d297749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33049, d297749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33049, d297749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33050 q = 1) (hb : d310056 q = 1) : d297750 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33050, d297750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33050, d297750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80717 (p : Pattern) (ha : d33146 p = 1) (hb : d310056 p = 1) : d297793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33051 q = 1) (hb : d310056 q = 1) : d297751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33051, d297751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80716 q ha hb
    | true =>
      simp only [d33051, d297751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33052 q = 1) (hb : d310056 q = 1) : d297752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33052, d297752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33052, d297752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33143 q = 1) (hb : d310056 q = 1) : d297790 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33143, d297790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33143, d297790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33144 q = 1) (hb : d310056 q = 1) : d297791 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33144, d297791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33144, d297791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33145 q = 1) (hb : d310056 q = 1) : d297792 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33145, d297792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d33145, d297792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d33146 q = 1) (hb : d310056 q = 1) : d297793 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33146, d297793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33146, d297793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80718 (p : Pattern) (ha : d33152 p = 1) (hb : d310056 p = 1) : d297799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33147 q = 1) (hb : d310056 q = 1) : d297794 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d33147, d297794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80717 q ha hb
    | true =>
      simp only [d33147, d297794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33148 q = 1) (hb : d310056 q = 1) : d297795 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d33148, d297795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33148, d297795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33149 q = 1) (hb : d310056 q = 1) : d297796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d33149, d297796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33149, d297796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33150 q = 1) (hb : d310056 q = 1) : d297797 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d33150, d297797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33150, d297797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33151 q = 1) (hb : d310056 q = 1) : d297798 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d33151, d297798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33151, d297798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33152 q = 1) (hb : d310056 q = 1) : d297799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d33152, d297799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33152, d297799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80719 (p : Pattern) (ha : d32786 p = 1) (hb : d310056 p = 1) : d297585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32752 q = 1) (hb : d310056 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80703 q ha hb
    | true =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32753 q = 1) (hb : d310056 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32758 q = 1) (hb : d310056 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32759 q = 1) (hb : d310056 q = 1) : d297558 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32759, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32759, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32785 q = 1) (hb : d310056 q = 1) : d297584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32785, d297584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32785, d297584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32786 q = 1) (hb : d310056 q = 1) : d297585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32786, d297585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32786, d297585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80720 (p : Pattern) (ha : d32788 p = 1) (hb : d310056 p = 1) : d297587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32762 q = 1) (hb : d310056 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32763 q = 1) (hb : d310056 q = 1) : d297562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32763, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32763, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32787 q = 1) (hb : d310056 q = 1) : d297586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32787, d297586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32787, d297586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32788 q = 1) (hb : d310056 q = 1) : d297587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32788, d297587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32788, d297587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80721 (p : Pattern) (ha : d32795 p = 1) (hb : d310056 p = 1) : d297594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32752 q = 1) (hb : d310056 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80703 q ha hb
    | true =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32753 q = 1) (hb : d310056 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32758 q = 1) (hb : d310056 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32793 q = 1) (hb : d310056 q = 1) : d297592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32793, d297592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32793, d297592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32794 q = 1) (hb : d310056 q = 1) : d297593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32794, d297593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32794, d297593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32795 q = 1) (hb : d310056 q = 1) : d297594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32795, d297594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32795, d297594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80722 (p : Pattern) (ha : d32798 p = 1) (hb : d310056 p = 1) : d297597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32762 q = 1) (hb : d310056 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32796 q = 1) (hb : d310056 q = 1) : d297595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32796, d297595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32796, d297595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32797 q = 1) (hb : d310056 q = 1) : d297596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32797, d297596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32797, d297596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32798 q = 1) (hb : d310056 q = 1) : d297597 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32798, d297597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32798, d297597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80723 (p : Pattern) (ha : d32803 p = 1) (hb : d310056 p = 1) : d281801 p = 1 := by
  have h0 (q : Pattern) (ha : d32802 q = 1) (hb : d310056 q = 1) : d32802 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32697 q = 1) (hb : d310056 q = 1) : d32697 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32708 q = 1) (hb : d310056 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
    | true =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32709 q = 1) (hb : d310056 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d32710 q = 1) (hb : d310056 q = 1) : d281714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32710, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32711 q = 1) (hb : d310056 q = 1) : d281715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32711, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d32712 q = 1) (hb : d310056 q = 1) : d281716 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32712, d281716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32712, d281716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32803 q = 1) (hb : d310056 q = 1) : d281801 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32803, d281801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32803, d281801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80724 (p : Pattern) (ha : d32807 p = 1) (hb : d310056 p = 1) : d297604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32708 q = 1) (hb : d310056 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
    | true =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32709 q = 1) (hb : d310056 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32710 q = 1) (hb : d310056 q = 1) : d281714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32710, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32710, d281714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32711 q = 1) (hb : d310056 q = 1) : d281715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32711, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32711, d281715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32716 q = 1) (hb : d310056 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
    | true =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32717 q = 1) (hb : d310056 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32718 q = 1) (hb : d310056 q = 1) : d297519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32718, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32718, d297519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32719 q = 1) (hb : d310056 q = 1) : d297520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32719, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32719, d297520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32720 q = 1) (hb : d310056 q = 1) : d297521 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32720, d297521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32720, d297521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32738 q = 1) (hb : d310056 q = 1) : d297537 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32738, d297537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32738, d297537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32807 q = 1) (hb : d310056 q = 1) : d297604 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32807, d297604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32807, d297604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro80725 (p : Pattern) (ha : d32813 p = 1) (hb : d310056 p = 1) : d297610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32804 q = 1) (hb : d310056 q = 1) : d297601 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32804, d297601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80723 q ha hb
    | true =>
      simp only [d32804, d297601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80698 q ha hb
  have h2 (q : Pattern) (ha : d32805 q = 1) (hb : d310056 q = 1) : d297602 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32805, d297602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32805, d297602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32806 q = 1) (hb : d310056 q = 1) : d297603 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32806, d297603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32806, d297603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32808 q = 1) (hb : d310056 q = 1) : d297605 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32808, d297605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80698 q ha hb
    | true =>
      simp only [d32808, d297605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80724 q ha hb
  have h5 (q : Pattern) (ha : d32809 q = 1) (hb : d310056 q = 1) : d297606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32809, d297606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32809, d297606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32810 q = 1) (hb : d310056 q = 1) : d297607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32810, d297607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32810, d297607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32811 q = 1) (hb : d310056 q = 1) : d297608 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32811, d297608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32811, d297608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32740 q = 1) (hb : d310056 q = 1) : d297539 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32740, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80698 q ha hb
    | true =>
      simp only [d32740, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80701 q ha hb
  have h9 (q : Pattern) (ha : d32741 q = 1) (hb : d310056 q = 1) : d297540 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32741, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32741, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32742 q = 1) (hb : d310056 q = 1) : d297541 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32742, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32742, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32745 q = 1) (hb : d310056 q = 1) : d297544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32745, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80701 q ha hb
    | true =>
      simp only [d32745, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80702 q ha hb
  have h12 (q : Pattern) (ha : d32746 q = 1) (hb : d310056 q = 1) : d297545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32746, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32746, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32747 q = 1) (hb : d310056 q = 1) : d297546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32747, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32747, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32748 q = 1) (hb : d310056 q = 1) : d297547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32748, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32748, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32812 q = 1) (hb : d310056 q = 1) : d297609 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32812, d297609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32812, d297609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32813 q = 1) (hb : d310056 q = 1) : d297610 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32813, d297610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32813, d297610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro80726 (p : Pattern) (ha : d32819 p = 1) (hb : d310056 p = 1) : d297616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32814 q = 1) (hb : d310056 q = 1) : d297611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32814, d297611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80725 q ha hb
    | true =>
      simp only [d32814, d297611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32815 q = 1) (hb : d310056 q = 1) : d297612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32815, d297612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32815, d297612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32752 q = 1) (hb : d310056 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80703 q ha hb
    | true =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32753 q = 1) (hb : d310056 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32816 q = 1) (hb : d310056 q = 1) : d297613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32816, d297613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32816, d297613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32817 q = 1) (hb : d310056 q = 1) : d297614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32817, d297614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32817, d297614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32818 q = 1) (hb : d310056 q = 1) : d297615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32818, d297615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32818, d297615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32819 q = 1) (hb : d310056 q = 1) : d297616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32819, d297616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32819, d297616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80727 (p : Pattern) (ha : d32905 p = 1) (hb : d310056 p = 1) : d297619 p = 1 := by
  have h0 (q : Pattern) (ha : d32687 q = 1) (hb : d202304 q = 1) : d32687 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32699 q = 1) (hb : d310056 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76289 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h4 (q : Pattern) (ha : d32700 q = 1) (hb : d310056 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32902 q = 1) (hb : d310056 q = 1) : d281820 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32902, d281820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32902, d281820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32903 q = 1) (hb : d310056 q = 1) : d281821 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32903, d281821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32903, d281821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d32904 q = 1) (hb : d310056 q = 1) : d281822 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32904, d281822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32904, d281822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h9 (q : Pattern) (ha : d5245 q = 1) (hb : d310056 q = 1) : d5245 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32905 q = 1) (hb : d310056 q = 1) : d297619 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32905, d297619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32905, d297619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80728 (p : Pattern) (ha : d32911 p = 1) (hb : d310056 p = 1) : d297625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32728 q = 1) (hb : d310056 q = 1) : d297527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32728, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80699 q ha hb
    | true =>
      simp only [d32728, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32729 q = 1) (hb : d310056 q = 1) : d297528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32729, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32729, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32730 q = 1) (hb : d310056 q = 1) : d297529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32730, d297529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32730, d297529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32731 q = 1) (hb : d310056 q = 1) : d297530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32731, d297530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32731, d297530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32733 q = 1) (hb : d310056 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
    | true =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32734 q = 1) (hb : d310056 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32735 q = 1) (hb : d310056 q = 1) : d297534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32735, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32735, d297534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32736 q = 1) (hb : d310056 q = 1) : d297535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32736, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32736, d297535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32737 q = 1) (hb : d310056 q = 1) : d297536 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32737, d297536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32737, d297536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32906 q = 1) (hb : d310056 q = 1) : d297620 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32906, d297620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80727 q ha hb
    | true =>
      simp only [d32906, d297620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32907 q = 1) (hb : d310056 q = 1) : d297621 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32907, d297621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32907, d297621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32908 q = 1) (hb : d310056 q = 1) : d297622 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32908, d297622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32908, d297622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32909 q = 1) (hb : d310056 q = 1) : d297623 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32909, d297623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32909, d297623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32910 q = 1) (hb : d310056 q = 1) : d297624 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32910, d297624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32910, d297624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32911 q = 1) (hb : d310056 q = 1) : d297625 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32911, d297625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32911, d297625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80729 (p : Pattern) (ha : d32915 p = 1) (hb : d310056 p = 1) : d297629 p = 1 := by
  have h0 (q : Pattern) (ha : d32687 q = 1) (hb : d202304 q = 1) : d32687 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32699 q = 1) (hb : d310056 q = 1) : d32688 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32699, d310056, d32688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76289 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d202304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10055 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10055, d310056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76221 q ha hb
  have h4 (q : Pattern) (ha : d32700 q = 1) (hb : d310056 q = 1) : d32689 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32700, d32689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5239 q = 1) (hb : d310056 q = 1) : d5239 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32912 q = 1) (hb : d310056 q = 1) : d297626 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32912, d297626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32912, d297626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30103 q = 1) (hb : d310056 q = 1) : d30103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32913 q = 1) (hb : d310056 q = 1) : d297627 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32913, d297627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32913, d297627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32914 q = 1) (hb : d310056 q = 1) : d297628 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32914, d297628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32914, d297628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5245 q = 1) (hb : d310056 q = 1) : d5245 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32915 q = 1) (hb : d310056 q = 1) : d297629 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32915, d297629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32915, d297629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro80730 (p : Pattern) (ha : d32921 p = 1) (hb : d310056 p = 1) : d297635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32916 q = 1) (hb : d310056 q = 1) : d297630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32916, d297630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80729 q ha hb
    | true =>
      simp only [d32916, d297630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32917 q = 1) (hb : d310056 q = 1) : d297631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32917, d297631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32917, d297631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32918 q = 1) (hb : d310056 q = 1) : d297632 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32918, d297632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32918, d297632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32919 q = 1) (hb : d310056 q = 1) : d297633 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32919, d297633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32919, d297633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32920 q = 1) (hb : d310056 q = 1) : d297634 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32920, d297634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32920, d297634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32921 q = 1) (hb : d310056 q = 1) : d297635 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32921, d297635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32921, d297635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80731 (p : Pattern) (ha : d32927 p = 1) (hb : d310056 p = 1) : d297641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32740 q = 1) (hb : d310056 q = 1) : d297539 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32740, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80698 q ha hb
    | true =>
      simp only [d32740, d297539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80701 q ha hb
  have h2 (q : Pattern) (ha : d32741 q = 1) (hb : d310056 q = 1) : d297540 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32741, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32741, d297540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32742 q = 1) (hb : d310056 q = 1) : d297541 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32742, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32742, d297541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32745 q = 1) (hb : d310056 q = 1) : d297544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32745, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80701 q ha hb
    | true =>
      simp only [d32745, d297544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80702 q ha hb
  have h5 (q : Pattern) (ha : d32746 q = 1) (hb : d310056 q = 1) : d297545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32746, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32746, d297545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32747 q = 1) (hb : d310056 q = 1) : d297546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32747, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32747, d297546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32748 q = 1) (hb : d310056 q = 1) : d297547 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32748, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32748, d297547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32922 q = 1) (hb : d310056 q = 1) : d297636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32922, d297636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80728 q ha hb
    | true =>
      simp only [d32922, d297636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80730 q ha hb
  have h9 (q : Pattern) (ha : d32923 q = 1) (hb : d310056 q = 1) : d297637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32923, d297637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32923, d297637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32924 q = 1) (hb : d310056 q = 1) : d297638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32924, d297638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32924, d297638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32925 q = 1) (hb : d310056 q = 1) : d297639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32925, d297639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32925, d297639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32926 q = 1) (hb : d310056 q = 1) : d297640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32926, d297640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32926, d297640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32927 q = 1) (hb : d310056 q = 1) : d297641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32927, d297641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32927, d297641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro80732 (p : Pattern) (ha : d32933 p = 1) (hb : d310056 p = 1) : d297647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32928 q = 1) (hb : d310056 q = 1) : d297642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32928, d297642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80731 q ha hb
    | true =>
      simp only [d32928, d297642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32929 q = 1) (hb : d310056 q = 1) : d297643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32929, d297643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32929, d297643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32930 q = 1) (hb : d310056 q = 1) : d297644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32930, d297644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32930, d297644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32931 q = 1) (hb : d310056 q = 1) : d297645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32931, d297645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32931, d297645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32932 q = 1) (hb : d310056 q = 1) : d297646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32932, d297646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32932, d297646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32933 q = 1) (hb : d310056 q = 1) : d297647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32933, d297647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32933, d297647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro80733 (p : Pattern) (ha : d245597 p = 1) (hb : d310056 p = 1) : d297653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32789 q = 1) (hb : d310056 q = 1) : d297588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32789, d297588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80719 q ha hb
    | true =>
      simp only [d32789, d297588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80720 q ha hb
  have h2 (q : Pattern) (ha : d32790 q = 1) (hb : d310056 q = 1) : d297589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32790, d297589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32790, d297589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32791 q = 1) (hb : d310056 q = 1) : d297590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32791, d297590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32791, d297590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32792 q = 1) (hb : d310056 q = 1) : d297591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32792, d297591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32792, d297591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32799 q = 1) (hb : d310056 q = 1) : d297598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32799, d297598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80721 q ha hb
    | true =>
      simp only [d32799, d297598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80722 q ha hb
  have h6 (q : Pattern) (ha : d32800 q = 1) (hb : d310056 q = 1) : d297599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32800, d297599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32800, d297599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32801 q = 1) (hb : d310056 q = 1) : d297600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32801, d297600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32801, d297600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32820 q = 1) (hb : d310056 q = 1) : d297617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32820, d297617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80726 q ha hb
    | true =>
      simp only [d32820, d297617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80705 q ha hb
  have h9 (q : Pattern) (ha : d245593 q = 1) (hb : d310056 q = 1) : d297618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d297618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245593, d297618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d32934 q = 1) (hb : d310056 q = 1) : d297648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32934, d297648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80732 q ha hb
    | true =>
      simp only [d32934, d297648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32935 q = 1) (hb : d310056 q = 1) : d297649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32935, d297649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32935, d297649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245594 q = 1) (hb : d310056 q = 1) : d297650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d297650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245594, d297650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245595 q = 1) (hb : d310056 q = 1) : d297651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d297651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245595, d297651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245596 q = 1) (hb : d310056 q = 1) : d297652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d297652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245596, d297652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d245597 q = 1) (hb : d310056 q = 1) : d297653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245597, d297653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245597, d297653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80734 (p : Pattern) (ha : d32940 p = 1) (hb : d310056 p = 1) : d297654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32752 q = 1) (hb : d310056 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80703 q ha hb
    | true =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32753 q = 1) (hb : d310056 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32758 q = 1) (hb : d310056 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32759 q = 1) (hb : d310056 q = 1) : d297558 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32759, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32759, d297558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32785 q = 1) (hb : d310056 q = 1) : d297584 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32785, d297584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32785, d297584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32940 q = 1) (hb : d310056 q = 1) : d297654 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32940, d297654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32940, d297654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80735 (p : Pattern) (ha : d32941 p = 1) (hb : d310056 p = 1) : d297655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32762 q = 1) (hb : d310056 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32763 q = 1) (hb : d310056 q = 1) : d297562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32763, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32763, d297562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32787 q = 1) (hb : d310056 q = 1) : d297586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32787, d297586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32787, d297586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32941 q = 1) (hb : d310056 q = 1) : d297655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32941, d297655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32941, d297655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80736 (p : Pattern) (ha : d32946 p = 1) (hb : d310056 p = 1) : d297660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32752 q = 1) (hb : d310056 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80703 q ha hb
    | true =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32753 q = 1) (hb : d310056 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32758 q = 1) (hb : d310056 q = 1) : d297557 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32758, d297557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32793 q = 1) (hb : d310056 q = 1) : d297592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32793, d297592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32793, d297592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32794 q = 1) (hb : d310056 q = 1) : d297593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32794, d297593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32794, d297593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32946 q = 1) (hb : d310056 q = 1) : d297660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32946, d297660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32946, d297660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80737 (p : Pattern) (ha : d32947 p = 1) (hb : d310056 p = 1) : d297661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32756 q = 1) (hb : d310056 q = 1) : d297555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80704 q ha hb
    | true =>
      simp only [d32756, d297555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32757 q = 1) (hb : d310056 q = 1) : d297556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32757, d297556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32762 q = 1) (hb : d310056 q = 1) : d297561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32762, d297561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32796 q = 1) (hb : d310056 q = 1) : d297595 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32796, d297595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32796, d297595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32797 q = 1) (hb : d310056 q = 1) : d297596 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32797, d297596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32797, d297596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32947 q = 1) (hb : d310056 q = 1) : d297661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32947, d297661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32947, d297661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80738 (p : Pattern) (ha : d32951 p = 1) (hb : d310056 p = 1) : d297665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32814 q = 1) (hb : d310056 q = 1) : d297611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32814, d297611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80725 q ha hb
    | true =>
      simp only [d32814, d297611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32815 q = 1) (hb : d310056 q = 1) : d297612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32815, d297612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32815, d297612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32752 q = 1) (hb : d310056 q = 1) : d297551 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80703 q ha hb
    | true =>
      simp only [d32752, d297551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32753 q = 1) (hb : d310056 q = 1) : d297552 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32753, d297552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32816 q = 1) (hb : d310056 q = 1) : d297613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32816, d297613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32816, d297613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32817 q = 1) (hb : d310056 q = 1) : d297614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32817, d297614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32817, d297614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32818 q = 1) (hb : d310056 q = 1) : d297615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32818, d297615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32818, d297615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32951 q = 1) (hb : d310056 q = 1) : d297665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32951, d297665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32951, d297665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80739 (p : Pattern) (ha : d32957 p = 1) (hb : d310056 p = 1) : d297668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32928 q = 1) (hb : d310056 q = 1) : d297642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32928, d297642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80731 q ha hb
    | true =>
      simp only [d32928, d297642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32929 q = 1) (hb : d310056 q = 1) : d297643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32929, d297643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32929, d297643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32930 q = 1) (hb : d310056 q = 1) : d297644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32930, d297644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32930, d297644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32931 q = 1) (hb : d310056 q = 1) : d297645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32931, d297645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32931, d297645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32932 q = 1) (hb : d310056 q = 1) : d297646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32932, d297646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32932, d297646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32957 q = 1) (hb : d310056 q = 1) : d297668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32957, d297668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32957, d297668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro80740 (p : Pattern) (ha : d245602 p = 1) (hb : d310056 p = 1) : d297674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32789 q = 1) (hb : d310056 q = 1) : d297588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32789, d297588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80719 q ha hb
    | true =>
      simp only [d32789, d297588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80720 q ha hb
  have h2 (q : Pattern) (ha : d32790 q = 1) (hb : d310056 q = 1) : d297589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32790, d297589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32790, d297589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32791 q = 1) (hb : d310056 q = 1) : d297590 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32791, d297590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32791, d297590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32792 q = 1) (hb : d310056 q = 1) : d297591 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32792, d297591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32792, d297591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32799 q = 1) (hb : d310056 q = 1) : d297598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32799, d297598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80721 q ha hb
    | true =>
      simp only [d32799, d297598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80722 q ha hb
  have h6 (q : Pattern) (ha : d32800 q = 1) (hb : d310056 q = 1) : d297599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32800, d297599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32800, d297599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32801 q = 1) (hb : d310056 q = 1) : d297600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32801, d297600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32801, d297600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32820 q = 1) (hb : d310056 q = 1) : d297617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32820, d297617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80726 q ha hb
    | true =>
      simp only [d32820, d297617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80705 q ha hb
  have h9 (q : Pattern) (ha : d245593 q = 1) (hb : d310056 q = 1) : d297618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245593, d297618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245593, d297618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d32934 q = 1) (hb : d310056 q = 1) : d297648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32934, d297648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80732 q ha hb
    | true =>
      simp only [d32934, d297648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32935 q = 1) (hb : d310056 q = 1) : d297649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32935, d297649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32935, d297649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d245594 q = 1) (hb : d310056 q = 1) : d297650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245594, d297650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245594, d297650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d245595 q = 1) (hb : d310056 q = 1) : d297651 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245595, d297651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245595, d297651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d245596 q = 1) (hb : d310056 q = 1) : d297652 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245596, d297652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d245596, d297652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32942 q = 1) (hb : d310056 q = 1) : d297656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32942, d297656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80734 q ha hb
    | true =>
      simp only [d32942, d297656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80735 q ha hb
  have h16 (q : Pattern) (ha : d32943 q = 1) (hb : d310056 q = 1) : d297657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32943, d297657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32943, d297657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32944 q = 1) (hb : d310056 q = 1) : d297658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32944, d297658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32944, d297658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32945 q = 1) (hb : d310056 q = 1) : d297659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32945, d297659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32945, d297659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32948 q = 1) (hb : d310056 q = 1) : d297662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32948, d297662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80736 q ha hb
    | true =>
      simp only [d32948, d297662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80737 q ha hb
  have h20 (q : Pattern) (ha : d32949 q = 1) (hb : d310056 q = 1) : d297663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32949, d297663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32949, d297663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d32950 q = 1) (hb : d310056 q = 1) : d297664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32950, d297664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d32950, d297664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d32952 q = 1) (hb : d310056 q = 1) : d297666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32952, d297666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80738 q ha hb
    | true =>
      simp only [d32952, d297666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80708 q ha hb
  have h23 (q : Pattern) (ha : d245598 q = 1) (hb : d310056 q = 1) : d297667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d297667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245598, d297667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d32958 q = 1) (hb : d310056 q = 1) : d297669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32958, d297669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80739 q ha hb
    | true =>
      simp only [d32958, d297669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d32959 q = 1) (hb : d310056 q = 1) : d297670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32959, d297670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d32959, d297670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d245599 q = 1) (hb : d310056 q = 1) : d297671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d297671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245599, d297671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d245600 q = 1) (hb : d310056 q = 1) : d297672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245600, d297672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245600, d297672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d245601 q = 1) (hb : d310056 q = 1) : d297673 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245601, d297673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245601, d297673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d245602 q = 1) (hb : d310056 q = 1) : d297674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245602, d297674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245602, d297674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro80741 (p : Pattern) (ha : d245609 p = 1) (hb : d310056 p = 1) : d297694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32952 q = 1) (hb : d310056 q = 1) : d297666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32952, d297666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80738 q ha hb
    | true =>
      simp only [d32952, d297666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80708 q ha hb
  have h2 (q : Pattern) (ha : d245598 q = 1) (hb : d310056 q = 1) : d297667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245598, d297667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245598, d297667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32958 q = 1) (hb : d310056 q = 1) : d297669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32958, d297669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80739 q ha hb
    | true =>
      simp only [d32958, d297669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32959 q = 1) (hb : d310056 q = 1) : d297670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32959, d297670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32959, d297670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d245599 q = 1) (hb : d310056 q = 1) : d297671 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245599, d297671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245599, d297671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d245607 q = 1) (hb : d310056 q = 1) : d297692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245607, d297692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245607, d297692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d245608 q = 1) (hb : d310056 q = 1) : d297693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245608, d297693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245608, d297693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d245609 q = 1) (hb : d310056 q = 1) : d297694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245609, d297694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d245609, d297694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro80742 (p : Pattern) (ha : d33001 p = 1) (hb : d310056 p = 1) : d281910 p = 1 := by
  have h0 (q : Pattern) (ha : d32995 q = 1) (hb : d310056 q = 1) : d32995 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32994 q = 1) (hb : d310056 q = 1) : d32994 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32996 q = 1) (hb : d310056 q = 1) : d281905 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32996, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
  have h4 (q : Pattern) (ha : d32708 q = 1) (hb : d310056 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
    | true =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d32997 q = 1) (hb : d310056 q = 1) : d281906 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32997, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32709 q = 1) (hb : d310056 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d32998 q = 1) (hb : d310056 q = 1) : d281907 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32998, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32999 q = 1) (hb : d310056 q = 1) : d281908 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32999, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d33000 q = 1) (hb : d310056 q = 1) : d281909 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33000, d281909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33000, d281909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33001 q = 1) (hb : d310056 q = 1) : d281910 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33001, d281910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33001, d281910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro80743 (p : Pattern) (ha : d33007 p = 1) (hb : d310056 p = 1) : d297707 p = 1 := by
  have h0 (q : Pattern) (ha : d32994 q = 1) (hb : d310056 q = 1) : d32994 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32996 q = 1) (hb : d310056 q = 1) : d281905 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32996, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
  have h3 (q : Pattern) (ha : d32708 q = 1) (hb : d310056 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
    | true =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d32997 q = 1) (hb : d310056 q = 1) : d281906 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32997, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32709 q = 1) (hb : d310056 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d32998 q = 1) (hb : d310056 q = 1) : d281907 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32998, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32999 q = 1) (hb : d310056 q = 1) : d281908 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32999, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d33000 q = 1) (hb : d310056 q = 1) : d281909 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33000, d281909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33000, d281909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33002 q = 1) (hb : d310056 q = 1) : d297702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33002, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33002, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
  have h10 (q : Pattern) (ha : d32716 q = 1) (hb : d310056 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
    | true =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d33003 q = 1) (hb : d310056 q = 1) : d297703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33003, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33003, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32717 q = 1) (hb : d310056 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d33004 q = 1) (hb : d310056 q = 1) : d297704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33004, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33004, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33005 q = 1) (hb : d310056 q = 1) : d297705 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33005, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33005, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d33006 q = 1) (hb : d310056 q = 1) : d297706 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33006, d297706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33006, d297706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33007 q = 1) (hb : d310056 q = 1) : d297707 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33007, d297707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d33007, d297707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro80744 (p : Pattern) (ha : d33012 p = 1) (hb : d310056 p = 1) : d297712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32996 q = 1) (hb : d310056 q = 1) : d281905 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32996, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32996, d281905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
  have h2 (q : Pattern) (ha : d32708 q = 1) (hb : d310056 q = 1) : d281712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80696 q ha hb
    | true =>
      simp only [d32708, d281712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32997 q = 1) (hb : d310056 q = 1) : d281906 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32997, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32997, d281906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32709 q = 1) (hb : d310056 q = 1) : d281713 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32709, d281713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32998 q = 1) (hb : d310056 q = 1) : d281907 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32998, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32998, d281907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32999 q = 1) (hb : d310056 q = 1) : d281908 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32999, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32999, d281908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33002 q = 1) (hb : d310056 q = 1) : d297702 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33002, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33002, d297702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
  have h8 (q : Pattern) (ha : d32716 q = 1) (hb : d310056 q = 1) : d297517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80697 q ha hb
    | true =>
      simp only [d32716, d297517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33003 q = 1) (hb : d310056 q = 1) : d297703 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33003, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33003, d297703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32717 q = 1) (hb : d310056 q = 1) : d297518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32717, d297518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33004 q = 1) (hb : d310056 q = 1) : d297704 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33004, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33004, d297704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33005 q = 1) (hb : d310056 q = 1) : d297705 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33005, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33005, d297705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33006 q = 1) (hb : d310056 q = 1) : d297706 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33006, d297706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33006, d297706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33011 q = 1) (hb : d310056 q = 1) : d297711 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33011, d297711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d33011, d297711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d33012 q = 1) (hb : d310056 q = 1) : d297712 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33012, d297712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33012, d297712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro80745 (p : Pattern) (ha : d33037 p = 1) (hb : d310056 p = 1) : d297737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33008 q = 1) (hb : d310056 q = 1) : d297708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33008, d297708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80742 q ha hb
    | true =>
      simp only [d33008, d297708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80743 q ha hb
  have h2 (q : Pattern) (ha : d33009 q = 1) (hb : d310056 q = 1) : d297709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33009, d297709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33009, d297709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33010 q = 1) (hb : d310056 q = 1) : d297710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33010, d297710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33010, d297710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33013 q = 1) (hb : d310056 q = 1) : d297713 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33013, d297713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80743 q ha hb
    | true =>
      simp only [d33013, d297713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80744 q ha hb
  have h5 (q : Pattern) (ha : d33014 q = 1) (hb : d310056 q = 1) : d297714 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33014, d297714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33014, d297714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33015 q = 1) (hb : d310056 q = 1) : d297715 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33015, d297715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33015, d297715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33016 q = 1) (hb : d310056 q = 1) : d297716 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33016, d297716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33016, d297716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33027 q = 1) (hb : d310056 q = 1) : d297727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33027, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80743 q ha hb
    | true =>
      simp only [d33027, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80714 q ha hb
  have h9 (q : Pattern) (ha : d33028 q = 1) (hb : d310056 q = 1) : d297728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33028, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33028, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33029 q = 1) (hb : d310056 q = 1) : d297729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33029, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33029, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d33032 q = 1) (hb : d310056 q = 1) : d297732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33032, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80714 q ha hb
    | true =>
      simp only [d33032, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80715 q ha hb
  have h12 (q : Pattern) (ha : d33033 q = 1) (hb : d310056 q = 1) : d297733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33033, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33033, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d33034 q = 1) (hb : d310056 q = 1) : d297734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33034, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33034, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33035 q = 1) (hb : d310056 q = 1) : d297735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33035, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d33035, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d33036 q = 1) (hb : d310056 q = 1) : d297736 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33036, d297736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33036, d297736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d33037 q = 1) (hb : d310056 q = 1) : d297737 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33037, d297737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d33037, d297737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro80746 (p : Pattern) (ha : d33042 p = 1) (hb : d310056 p = 1) : d297742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33027 q = 1) (hb : d310056 q = 1) : d297727 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33027, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80743 q ha hb
    | true =>
      simp only [d33027, d297727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80714 q ha hb
  have h2 (q : Pattern) (ha : d33028 q = 1) (hb : d310056 q = 1) : d297728 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33028, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33028, d297728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33029 q = 1) (hb : d310056 q = 1) : d297729 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33029, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33029, d297729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d33032 q = 1) (hb : d310056 q = 1) : d297732 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d33032, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80714 q ha hb
    | true =>
      simp only [d33032, d297732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80715 q ha hb
  have h5 (q : Pattern) (ha : d33033 q = 1) (hb : d310056 q = 1) : d297733 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d33033, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33033, d297733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33034 q = 1) (hb : d310056 q = 1) : d297734 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33034, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33034, d297734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33035 q = 1) (hb : d310056 q = 1) : d297735 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33035, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33035, d297735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33040 q = 1) (hb : d310056 q = 1) : d297740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d33040, d297740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33040, d297740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33041 q = 1) (hb : d310056 q = 1) : d297741 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d33041, d297741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33041, d297741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33042 q = 1) (hb : d310056 q = 1) : d297742 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d33042, d297742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33042, d297742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro80747 (p : Pattern) (ha : d33048 p = 1) (hb : d310056 p = 1) : d297748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33038 q = 1) (hb : d310056 q = 1) : d297738 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33038, d297738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80745 q ha hb
    | true =>
      simp only [d33038, d297738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33039 q = 1) (hb : d310056 q = 1) : d297739 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33039, d297739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33039, d297739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33043 q = 1) (hb : d310056 q = 1) : d297743 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33043, d297743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80746 q ha hb
    | true =>
      simp only [d33043, d297743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33044 q = 1) (hb : d310056 q = 1) : d297744 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33044, d297744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33044, d297744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33045 q = 1) (hb : d310056 q = 1) : d297745 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33045, d297745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33045, d297745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33046 q = 1) (hb : d310056 q = 1) : d297746 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33046, d297746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33046, d297746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33047 q = 1) (hb : d310056 q = 1) : d297747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33047, d297747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33047, d297747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33048 q = 1) (hb : d310056 q = 1) : d297748 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33048, d297748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33048, d297748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80748 (p : Pattern) (ha : d33056 p = 1) (hb : d310056 p = 1) : d297756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33043 q = 1) (hb : d310056 q = 1) : d297743 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33043, d297743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80746 q ha hb
    | true =>
      simp only [d33043, d297743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d33044 q = 1) (hb : d310056 q = 1) : d297744 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33044, d297744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33044, d297744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33051 q = 1) (hb : d310056 q = 1) : d297751 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d33051, d297751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80716 q ha hb
    | true =>
      simp only [d33051, d297751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d33052 q = 1) (hb : d310056 q = 1) : d297752 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d33052, d297752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33052, d297752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33053 q = 1) (hb : d310056 q = 1) : d297753 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d33053, d297753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d33053, d297753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33054 q = 1) (hb : d310056 q = 1) : d297754 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d33054, d297754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33054, d297754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33055 q = 1) (hb : d310056 q = 1) : d297755 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d33055, d297755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33055, d297755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d33056 q = 1) (hb : d310056 q = 1) : d297756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d33056, d297756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33056, d297756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro80749 (p : Pattern) (ha : d33117 p = 1) (hb : d310056 p = 1) : d297764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d310056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d33017 q = 1) (hb : d310056 q = 1) : d297717 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33017, d297717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33017, d297717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80699 q ha hb
  have h2 (q : Pattern) (ha : d32728 q = 1) (hb : d310056 q = 1) : d297527 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32728, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80699 q ha hb
    | true =>
      simp only [d32728, d297527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d33018 q = 1) (hb : d310056 q = 1) : d297718 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33018, d297718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d33018, d297718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32729 q = 1) (hb : d310056 q = 1) : d297528 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32729, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32729, d297528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d33019 q = 1) (hb : d310056 q = 1) : d297719 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33019, d297719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d33019, d297719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33020 q = 1) (hb : d310056 q = 1) : d297720 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33020, d297720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d33020, d297720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d33021 q = 1) (hb : d310056 q = 1) : d297721 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33021, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33021, d297721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
  have h8 (q : Pattern) (ha : d32733 q = 1) (hb : d310056 q = 1) : d297532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80700 q ha hb
    | true =>
      simp only [d32733, d297532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d33022 q = 1) (hb : d310056 q = 1) : d297722 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33022, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d33022, d297722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32734 q = 1) (hb : d310056 q = 1) : d297533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32734, d297533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d33023 q = 1) (hb : d310056 q = 1) : d297723 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33023, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d33023, d297723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33024 q = 1) (hb : d310056 q = 1) : d297724 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33024, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d33024, d297724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d33025 q = 1) (hb : d310056 q = 1) : d297725 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33025, d297725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d33025, d297725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d33112 q = 1) (hb : d310056 q = 1) : d297759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d33112, d297759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33112, d297759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80727 q ha hb
  have h15 (q : Pattern) (ha : d32906 q = 1) (hb : d310056 q = 1) : d297620 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32906, d297620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80727 q ha hb
    | true =>
      simp only [d32906, d297620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d33113 q = 1) (hb : d310056 q = 1) : d297760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d33113, d297760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d33113, d297760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32907 q = 1) (hb : d310056 q = 1) : d297621 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32907, d297621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32907, d297621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d33114 q = 1) (hb : d310056 q = 1) : d297761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d33114, d297761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d33114, d297761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d33115 q = 1) (hb : d310056 q = 1) : d297762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d33115, d297762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d33115, d297762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d33116 q = 1) (hb : d310056 q = 1) : d297763 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d33116, d297763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d33116, d297763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d33117 q = 1) (hb : d310056 q = 1) : d297764 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d33117, d297764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d33117, d297764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
end NetHack.Soko22Hazard87
