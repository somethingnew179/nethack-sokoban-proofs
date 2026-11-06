import NetHack.Soko22Hazard87.AndIntroBlocks0143
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro36000 (p : Pattern) (ha : d15134 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15129 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35999 q ha hb
    | true =>
      simp only [d15129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15130 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15131 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15132 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15133 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15134 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36001 (p : Pattern) (ha : d14819 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35985 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14819 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36002 (p : Pattern) (ha : d14821 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14821 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36003 (p : Pattern) (ha : d14828 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35985 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14828 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36004 (p : Pattern) (ha : d14831 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14831 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36005 (p : Pattern) (ha : d14850 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14841 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14842 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14842, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14842, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14846 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14847 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14847, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14847, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14848 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14768 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14769 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d14775 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14776 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d14777 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14849 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14850 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36006 (p : Pattern) (ha : d14861 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36005 q ha hb
    | true =>
      simp only [d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35993 q ha hb
    | true =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14861 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36007 (p : Pattern) (ha : d14916 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14768 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14769 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d14775 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14776 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d14777 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14912 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14913 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14913, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14913, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14914 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14915 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14916 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro36008 (p : Pattern) (ha : d14922 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36007 q ha hb
    | true =>
      simp only [d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14922 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36009 (p : Pattern) (ha : d125575 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36001 q ha hb
    | true =>
      simp only [d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36002 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36003 q ha hb
    | true =>
      simp only [d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36004 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36006 q ha hb
    | true =>
      simp only [d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35994 q ha hb
  have h9 (q : Pattern) (ha : d125571 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36008 q ha hb
    | true =>
      simp only [d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125572 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125573 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36010 (p : Pattern) (ha : d14929 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35985 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14929 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36011 (p : Pattern) (ha : d14930 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14930 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36012 (p : Pattern) (ha : d14935 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35985 q ha hb
    | true =>
      simp only [d14785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14935 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36013 (p : Pattern) (ha : d14936 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14936 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36014 (p : Pattern) (ha : d14940 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36005 q ha hb
    | true =>
      simp only [d14851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35993 q ha hb
    | true =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14940 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36015 (p : Pattern) (ha : d14941 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35993 q ha hb
    | true =>
      simp only [d14856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35986 q ha hb
    | true =>
      simp only [d14789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14941 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36016 (p : Pattern) (ha : d14947 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36007 q ha hb
    | true =>
      simp only [d14917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14947 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36017 (p : Pattern) (ha : d125580 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36001 q ha hb
    | true =>
      simp only [d14822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36002 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36003 q ha hb
    | true =>
      simp only [d14832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36004 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36006 q ha hb
    | true =>
      simp only [d14866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35994 q ha hb
  have h9 (q : Pattern) (ha : d125571 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36008 q ha hb
    | true =>
      simp only [d14923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125572 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125573 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14931 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36010 q ha hb
    | true =>
      simp only [d14931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36011 q ha hb
  have h16 (q : Pattern) (ha : d14932 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14933 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14934 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14937 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36012 q ha hb
    | true =>
      simp only [d14937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36013 q ha hb
  have h20 (q : Pattern) (ha : d14938 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14939 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14942 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36014 q ha hb
    | true =>
      simp only [d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36015 q ha hb
  have h23 (q : Pattern) (ha : d125576 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14948 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36016 q ha hb
    | true =>
      simp only [d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14949 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125577 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125578 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125579 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125580 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro36018 (p : Pattern) (ha : d125587 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14942 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36014 q ha hb
    | true =>
      simp only [d14942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36015 q ha hb
  have h2 (q : Pattern) (ha : d125576 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14948 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36016 q ha hb
    | true =>
      simp only [d14948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14949 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125577 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125585 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125586 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125587 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36019 (p : Pattern) (ha : d15030 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15001 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15002 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15002, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15002, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15011 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15012 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15012, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15012, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15013 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15017 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15018 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15026 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15027 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d15028 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15029 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15030 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36020 (p : Pattern) (ha : d15035 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15018 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15026 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15027 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15028 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15033 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15034 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15035 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro36021 (p : Pattern) (ha : d15041 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15031 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36019 q ha hb
    | true =>
      simp only [d15031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15032 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15036 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36020 q ha hb
    | true =>
      simp only [d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15037 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15038 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15039 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15040 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15041 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36022 (p : Pattern) (ha : d15054 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15036 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36020 q ha hb
    | true =>
      simp only [d15036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15037 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35998 q ha hb
    | true =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15051 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15052 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15053 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15054 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36023 (p : Pattern) (ha : d15111 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15018 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15026 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15027 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15028 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15107 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15108 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15108, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15108, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15109 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15110 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15111 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro36024 (p : Pattern) (ha : d15117 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15112 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36023 q ha hb
    | true =>
      simp only [d15112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15113 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15114 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15115 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15116 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15117 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36025 (p : Pattern) (ha : d125597 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15055 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36021 q ha hb
    | true =>
      simp only [d15055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36022 q ha hb
  have h2 (q : Pattern) (ha : d125593 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15118 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36024 q ha hb
    | true =>
      simp only [d15118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15119 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125594 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125595 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125596 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125597 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36026 (p : Pattern) (ha : d125603 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14805 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35989 q ha hb
  have h2 (q : Pattern) (ha : d14806 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14815 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35989 q ha hb
    | true =>
      simp only [d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35992 q ha hb
  have h4 (q : Pattern) (ha : d14816 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14817 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125581 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36009 q ha hb
    | true =>
      simp only [d125581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36017 q ha hb
  have h7 (q : Pattern) (ha : d14972 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35995 q ha hb
    | true =>
      simp only [d14972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35996 q ha hb
  have h8 (q : Pattern) (ha : d125582 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125583 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125584 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125588 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36018 q ha hb
  have h12 (q : Pattern) (ha : d14981 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35997 q ha hb
  have h13 (q : Pattern) (ha : d125589 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125590 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125591 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125592 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125598 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36025 q ha hb
  have h18 (q : Pattern) (ha : d15135 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36000 q ha hb
  have h19 (q : Pattern) (ha : d125599 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125600 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125601 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125602 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125603 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36027 (p : Pattern) (ha : d125609 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125604 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36026 q ha hb
  have h2 (q : Pattern) (ha : d125605 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125606 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125607 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125608 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125609 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36028 (p : Pattern) (ha : d15177 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15162 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15169 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15170 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15173 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15174 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15175 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15176 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15177 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro36029 (p : Pattern) (ha : d15181 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15173 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15174 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15175 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15180 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d15181 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro36030 (p : Pattern) (ha : d15187 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36028 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15187 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36031 (p : Pattern) (ha : d15191 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15191 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36032 (p : Pattern) (ha : d15197 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36030 q ha hb
    | true =>
      simp only [d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36031 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15197 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36033 (p : Pattern) (ha : d15200 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36028 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15200 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36034 (p : Pattern) (ha : d15201 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15201 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36035 (p : Pattern) (ha : d15207 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36030 q ha hb
    | true =>
      simp only [d15192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36031 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15202 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36033 q ha hb
    | true =>
      simp only [d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36034 q ha hb
  have h7 (q : Pattern) (ha : d15203 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15204 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15205 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15206 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15207 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36036 (p : Pattern) (ha : d15248 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15162 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15169 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15170 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15246 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15247 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15248 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro36037 (p : Pattern) (ha : d15258 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36036 q ha hb
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15258 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36038 (p : Pattern) (ha : d15358 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15348 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36037 q ha hb
    | true =>
      simp only [d15348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36031 q ha hb
  have h2 (q : Pattern) (ha : d15349 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15350 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15351 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15352 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15353 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36031 q ha hb
    | true =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15354 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15355 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15356 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15357 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15358 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36039 (p : Pattern) (ha : d15364 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15353 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36031 q ha hb
    | true =>
      simp only [d15353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15354 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15355 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15356 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15357 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15359 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36034 q ha hb
    | true =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15360 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15361 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15362 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15363 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15364 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36040 (p : Pattern) (ha : d15373 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15359 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36034 q ha hb
    | true =>
      simp only [d15359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15360 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15361 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15362 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15363 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15373 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36041 (p : Pattern) (ha : d15441 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15438 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15439 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15440 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d15441 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro36042 (p : Pattern) (ha : d15521 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15442 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36041 q ha hb
    | true =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15443 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15518 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15519 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15520 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15521 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36043 (p : Pattern) (ha : d15527 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15522 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36042 q ha hb
    | true =>
      simp only [d15522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15523 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15524 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15525 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15526 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15527 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36044 (p : Pattern) (ha : d15212 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36028 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15212 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36045 (p : Pattern) (ha : d15214 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15214 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36046 (p : Pattern) (ha : d15221 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36028 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15221 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36047 (p : Pattern) (ha : d15224 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15224 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36048 (p : Pattern) (ha : d15243 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15235 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15235, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15235, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15239 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15240 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15240, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15240, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15241 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15161 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15162 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15168 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15169 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d15170 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15242 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15243 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36049 (p : Pattern) (ha : d15254 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36048 q ha hb
    | true =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36036 q ha hb
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15254 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36050 (p : Pattern) (ha : d15309 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15161 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15162 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15169 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15170 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15305 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15306 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15306, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15306, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15307 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15308 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15309 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro36051 (p : Pattern) (ha : d15315 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36050 q ha hb
    | true =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15315 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36052 (p : Pattern) (ha : d125617 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36044 q ha hb
    | true =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36045 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36046 q ha hb
    | true =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36047 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36049 q ha hb
    | true =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36037 q ha hb
  have h9 (q : Pattern) (ha : d125613 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36051 q ha hb
    | true =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125614 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125615 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125616 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125617 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36053 (p : Pattern) (ha : d15322 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36028 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15322 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36054 (p : Pattern) (ha : d15323 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15323 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36055 (p : Pattern) (ha : d15328 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36028 q ha hb
    | true =>
      simp only [d15178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15328 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36056 (p : Pattern) (ha : d15329 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15329 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36057 (p : Pattern) (ha : d15333 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36048 q ha hb
    | true =>
      simp only [d15244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36036 q ha hb
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15333 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36058 (p : Pattern) (ha : d15334 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36036 q ha hb
    | true =>
      simp only [d15249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36029 q ha hb
    | true =>
      simp only [d15182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15334 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36059 (p : Pattern) (ha : d15340 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36050 q ha hb
    | true =>
      simp only [d15310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15340 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36060 (p : Pattern) (ha : d125622 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36044 q ha hb
    | true =>
      simp only [d15215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36045 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36046 q ha hb
    | true =>
      simp only [d15225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36047 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36049 q ha hb
    | true =>
      simp only [d15259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36037 q ha hb
  have h9 (q : Pattern) (ha : d125613 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36051 q ha hb
    | true =>
      simp only [d15316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125614 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125615 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125616 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15324 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36053 q ha hb
    | true =>
      simp only [d15324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36054 q ha hb
  have h16 (q : Pattern) (ha : d15325 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15326 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15327 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15330 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36055 q ha hb
    | true =>
      simp only [d15330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36056 q ha hb
  have h20 (q : Pattern) (ha : d15331 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15332 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15335 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36057 q ha hb
    | true =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36058 q ha hb
  have h23 (q : Pattern) (ha : d125618 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15341 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36059 q ha hb
    | true =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15342 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125619 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125620 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125621 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125622 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro36061 (p : Pattern) (ha : d125629 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15335 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36057 q ha hb
    | true =>
      simp only [d15335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36058 q ha hb
  have h2 (q : Pattern) (ha : d125618 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15341 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36059 q ha hb
    | true =>
      simp only [d15341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15342 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125619 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125627 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125628 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125629 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36062 (p : Pattern) (ha : d15423 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15395 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15395, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15395, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15404 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15405 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15405, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15405, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15406 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15410 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15411 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15419 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15420 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d15421 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15422 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15423 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36063 (p : Pattern) (ha : d15428 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15410 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15411 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15419 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15420 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15421 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15426 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15427 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15428 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro36064 (p : Pattern) (ha : d15434 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15424 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36062 q ha hb
    | true =>
      simp only [d15424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15425 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15429 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36063 q ha hb
    | true =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15430 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15431 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15432 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15433 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15434 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36065 (p : Pattern) (ha : d15447 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15429 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36063 q ha hb
    | true =>
      simp only [d15429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15430 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36041 q ha hb
    | true =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15444 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15445 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15446 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15447 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36066 (p : Pattern) (ha : d15504 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15410 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15411 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15419 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15420 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15421 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15500 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15501 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15501, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15501, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15502 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15503 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15504 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro36067 (p : Pattern) (ha : d15510 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15505 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36066 q ha hb
    | true =>
      simp only [d15505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15506 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15507 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15508 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15509 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15510 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36068 (p : Pattern) (ha : d125639 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15448 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36064 q ha hb
    | true =>
      simp only [d15448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36065 q ha hb
  have h2 (q : Pattern) (ha : d125635 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15511 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36067 q ha hb
    | true =>
      simp only [d15511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15512 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125636 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125637 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125638 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125639 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36069 (p : Pattern) (ha : d125645 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15198 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36032 q ha hb
  have h2 (q : Pattern) (ha : d15199 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15208 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36032 q ha hb
    | true =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36035 q ha hb
  have h4 (q : Pattern) (ha : d15209 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15210 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125623 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36052 q ha hb
    | true =>
      simp only [d125623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36060 q ha hb
  have h7 (q : Pattern) (ha : d15365 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36038 q ha hb
    | true =>
      simp only [d15365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36039 q ha hb
  have h8 (q : Pattern) (ha : d125624 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125625 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125626 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125630 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36061 q ha hb
  have h12 (q : Pattern) (ha : d15374 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36040 q ha hb
  have h13 (q : Pattern) (ha : d125631 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125632 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125633 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125634 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125640 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36068 q ha hb
  have h18 (q : Pattern) (ha : d15528 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36043 q ha hb
  have h19 (q : Pattern) (ha : d125641 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125642 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125643 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125644 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125645 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36070 (p : Pattern) (ha : d125651 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125646 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36069 q ha hb
  have h2 (q : Pattern) (ha : d125647 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125648 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125649 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125650 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125651 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36071 (p : Pattern) (ha : d15569 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15553 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15554 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15560 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15561 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15562 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15565 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15566 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15567 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15568 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15569 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro36072 (p : Pattern) (ha : d15573 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15565 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15566 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15567 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15572 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d15573 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro36073 (p : Pattern) (ha : d15579 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36071 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15579 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36074 (p : Pattern) (ha : d15583 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15583 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36075 (p : Pattern) (ha : d15589 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36073 q ha hb
    | true =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36074 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15589 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36076 (p : Pattern) (ha : d15592 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36071 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15592 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36077 (p : Pattern) (ha : d15593 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15593 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36078 (p : Pattern) (ha : d15599 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36073 q ha hb
    | true =>
      simp only [d15584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36074 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15594 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36076 q ha hb
    | true =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36077 q ha hb
  have h7 (q : Pattern) (ha : d15595 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15596 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15597 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15598 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15599 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36079 (p : Pattern) (ha : d15636 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15553 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15554 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15560 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15561 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15562 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15634 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15635 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15636 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro36080 (p : Pattern) (ha : d15646 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36079 q ha hb
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15646 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36081 (p : Pattern) (ha : d15746 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15736 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36080 q ha hb
    | true =>
      simp only [d15736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36074 q ha hb
  have h2 (q : Pattern) (ha : d15737 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15738 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15739 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15740 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15741 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36074 q ha hb
    | true =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15742 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15743 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15744 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15745 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15746 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36082 (p : Pattern) (ha : d15752 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15741 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36074 q ha hb
    | true =>
      simp only [d15741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15742 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15743 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15744 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15745 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15747 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36077 q ha hb
    | true =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15748 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15749 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15750 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15751 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15752 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36083 (p : Pattern) (ha : d15761 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15747 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36077 q ha hb
    | true =>
      simp only [d15747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15748 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15749 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15750 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15751 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15761 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36084 (p : Pattern) (ha : d15819 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15816 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15817 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15818 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d15819 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro36085 (p : Pattern) (ha : d15899 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15820 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36084 q ha hb
    | true =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15821 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15896 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15897 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15898 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15899 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36086 (p : Pattern) (ha : d15905 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15900 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36085 q ha hb
    | true =>
      simp only [d15900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15901 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15902 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15903 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15904 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15905 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36087 (p : Pattern) (ha : d15604 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36071 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15604 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36088 (p : Pattern) (ha : d15606 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15606 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36089 (p : Pattern) (ha : d15613 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36071 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15613 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36090 (p : Pattern) (ha : d15616 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15616 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36091 (p : Pattern) (ha : d15631 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15623 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15624 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15624, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15624, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15627 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15628 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15628, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15628, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15629 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15554 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15560 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15561 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d15562 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15630 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15631 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36092 (p : Pattern) (ha : d15642 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36091 q ha hb
    | true =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36079 q ha hb
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15642 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36093 (p : Pattern) (ha : d15697 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15553 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15554 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15560 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15561 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15562 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15693 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15694 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15694, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15694, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15695 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15696 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15697 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro36094 (p : Pattern) (ha : d15703 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36093 q ha hb
    | true =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15703 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36095 (p : Pattern) (ha : d125660 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36087 q ha hb
    | true =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36088 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36089 q ha hb
    | true =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36090 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36092 q ha hb
    | true =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36080 q ha hb
  have h9 (q : Pattern) (ha : d125656 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36094 q ha hb
    | true =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125657 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125658 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125659 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125660 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36096 (p : Pattern) (ha : d15710 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36071 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15710 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36097 (p : Pattern) (ha : d15711 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15711 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36098 (p : Pattern) (ha : d15716 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36071 q ha hb
    | true =>
      simp only [d15570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15716 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36099 (p : Pattern) (ha : d15717 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15717 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36100 (p : Pattern) (ha : d15721 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36091 q ha hb
    | true =>
      simp only [d15632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36079 q ha hb
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15721 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36101 (p : Pattern) (ha : d15722 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36079 q ha hb
    | true =>
      simp only [d15637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36072 q ha hb
    | true =>
      simp only [d15574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15722 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36102 (p : Pattern) (ha : d15728 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36093 q ha hb
    | true =>
      simp only [d15698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15728 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36103 (p : Pattern) (ha : d125665 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36087 q ha hb
    | true =>
      simp only [d15607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36088 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36089 q ha hb
    | true =>
      simp only [d15617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36090 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36092 q ha hb
    | true =>
      simp only [d15647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36080 q ha hb
  have h9 (q : Pattern) (ha : d125656 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36094 q ha hb
    | true =>
      simp only [d15704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125657 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125658 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125659 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15712 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36096 q ha hb
    | true =>
      simp only [d15712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36097 q ha hb
  have h16 (q : Pattern) (ha : d15713 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15714 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15715 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15718 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36098 q ha hb
    | true =>
      simp only [d15718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36099 q ha hb
  have h20 (q : Pattern) (ha : d15719 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15720 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15723 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36100 q ha hb
    | true =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36101 q ha hb
  have h23 (q : Pattern) (ha : d125661 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15729 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36102 q ha hb
    | true =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15730 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125662 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125663 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125664 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125665 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro36104 (p : Pattern) (ha : d125672 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15723 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36100 q ha hb
    | true =>
      simp only [d15723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36101 q ha hb
  have h2 (q : Pattern) (ha : d125661 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15729 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36102 q ha hb
    | true =>
      simp only [d15729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15730 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125662 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125670 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125671 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125672 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36105 (p : Pattern) (ha : d15801 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15774 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15774, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15774, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15782 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15783 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15783, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15783, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15784 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15788 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d15797 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15798 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d15799 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15800 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d15801 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36106 (p : Pattern) (ha : d15806 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15788 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15798 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15799 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15804 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15805 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15806 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro36107 (p : Pattern) (ha : d15812 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15802 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36105 q ha hb
    | true =>
      simp only [d15802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15803 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15807 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36106 q ha hb
    | true =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15808 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15809 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15810 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15811 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15812 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36108 (p : Pattern) (ha : d15825 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15807 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36106 q ha hb
    | true =>
      simp only [d15807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15808 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36084 q ha hb
    | true =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15822 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15823 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15824 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15825 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36109 (p : Pattern) (ha : d15882 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15788 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15798 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15799 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15878 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15879 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15879, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15879, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15880 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15881 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15882 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro36110 (p : Pattern) (ha : d15888 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15883 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36109 q ha hb
    | true =>
      simp only [d15883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15884 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15885 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15886 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15887 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15888 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36111 (p : Pattern) (ha : d125682 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15826 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36107 q ha hb
    | true =>
      simp only [d15826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36108 q ha hb
  have h2 (q : Pattern) (ha : d125678 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15889 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36110 q ha hb
    | true =>
      simp only [d15889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15890 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125679 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125680 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125681 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125682 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36112 (p : Pattern) (ha : d125688 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15590 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36075 q ha hb
  have h2 (q : Pattern) (ha : d15591 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15600 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36075 q ha hb
    | true =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36078 q ha hb
  have h4 (q : Pattern) (ha : d15601 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15602 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125666 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36095 q ha hb
    | true =>
      simp only [d125666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36103 q ha hb
  have h7 (q : Pattern) (ha : d15753 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36081 q ha hb
    | true =>
      simp only [d15753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36082 q ha hb
  have h8 (q : Pattern) (ha : d125667 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125668 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125669 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125673 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36104 q ha hb
  have h12 (q : Pattern) (ha : d15762 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36083 q ha hb
  have h13 (q : Pattern) (ha : d125674 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125675 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125676 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125677 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125683 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36111 q ha hb
  have h18 (q : Pattern) (ha : d15906 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36086 q ha hb
  have h19 (q : Pattern) (ha : d125684 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125685 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125686 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125687 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125688 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36113 (p : Pattern) (ha : d125694 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125689 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36112 q ha hb
  have h2 (q : Pattern) (ha : d125690 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125691 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125692 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125693 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125694 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36114 (p : Pattern) (ha : d125700 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d125529 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35908 q ha hb
    | true =>
      simp only [d125529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35946 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125569 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35984 q ha hb
  have h3 (q : Pattern) (ha : d125570 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125610 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36027 q ha hb
  have h5 (q : Pattern) (ha : d125611 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125612 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125652 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36070 q ha hb
  have h8 (q : Pattern) (ha : d125653 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125654 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125655 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125695 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36113 q ha hb
  have h12 (q : Pattern) (ha : d125696 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125697 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125698 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125699 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125700 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro36115 (p : Pattern) (ha : d125706 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125701 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36114 q ha hb
    | true =>
      simp only [d125701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125702 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125703 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125704 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125705 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125706 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36116 (p : Pattern) (ha : d125712 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125707 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36115 q ha hb
    | true =>
      simp only [d125707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125708 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125709 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125710 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125711 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125712 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36117 (p : Pattern) (ha : d125718 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125713 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36116 q ha hb
    | true =>
      simp only [d125713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125714 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125715 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125716 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125717 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125718 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36118 (p : Pattern) (ha : d125724 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125719 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36117 q ha hb
    | true =>
      simp only [d125719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125720 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125721 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125722 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125723 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125724 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36119 (p : Pattern) (ha : d125730 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125725 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36118 q ha hb
    | true =>
      simp only [d125725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125726 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125727 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125728 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125729 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125730 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36120 (p : Pattern) (ha : d125736 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125731 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36119 q ha hb
    | true =>
      simp only [d125731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125732 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125733 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125734 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125735 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125736 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36121 (p : Pattern) (ha : d125742 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125737 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36120 q ha hb
    | true =>
      simp only [d125737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125738 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125739 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125740 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125741 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125742 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36122 (p : Pattern) (ha : d53647 p = 1) (hb : d129472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35869 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35870 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35886 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35887 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
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
theorem andIntro36123 (p : Pattern) (ha : d129472 p = 1) (hb : d163447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14001 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35879 q ha hb
    | true =>
      simp only [d14001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35862 q ha hb
  have h2 (q : Pattern) (ha : d14057 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14058 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14059 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14060 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163447 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36124 (p : Pattern) (ha : d129472 p = 1) (hb : d163457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14033 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35883 q ha hb
    | true =>
      simp only [d14033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35866 q ha hb
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163454 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163455 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163456 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36125 (p : Pattern) (ha : d129472 p = 1) (hb : d163463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35888 q ha hb
    | true =>
      simp only [d14062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35889 q ha hb
  have h2 (q : Pattern) (ha : d14063 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163445 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163446 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163448 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36123 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163449 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163450 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163451 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129472 q = 1) (hb : d163452 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36124 q ha hb
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129472 q = 1) (hb : d163460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129472 q = 1) (hb : d163461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129472 q = 1) (hb : d163462 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129472 q = 1) (hb : d163463 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36126 (p : Pattern) (ha : d129472 p = 1) (hb : d163469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36122 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163464 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36125 q ha hb
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163465 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163466 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129472 q = 1) (hb : d163467 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163468 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163469 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d163469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36127 (p : Pattern) (ha : d129472 p = 1) (hb : d163472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14235 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35914 q ha hb
    | true =>
      simp only [d14235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35915 q ha hb
  have h2 (q : Pattern) (ha : d14236 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14237 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14238 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14239 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36128 (p : Pattern) (ha : d129472 p = 1) (hb : d163483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35942 q hb ha
    | true =>
      simp only [d163478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35921 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163481 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163482 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163483 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36129 (p : Pattern) (ha : d129472 p = 1) (hb : d163489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35913 q ha hb
    | true =>
      simp only [d14241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35916 q ha hb
  have h2 (q : Pattern) (ha : d14242 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36127 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129472 q = 1) (hb : d163477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163484 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36128 q ha hb
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163485 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129472 q = 1) (hb : d163486 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129472 q = 1) (hb : d163487 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129472 q = 1) (hb : d163488 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129472 q = 1) (hb : d163489 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36130 (p : Pattern) (ha : d129472 p = 1) (hb : d163495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163490 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36129 q ha hb
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163491 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163492 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163493 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163494 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163495 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36131 (p : Pattern) (ha : d129472 p = 1) (hb : d163499 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14502 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35952 q ha hb
    | true =>
      simp only [d14502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35953 q ha hb
  have h2 (q : Pattern) (ha : d14503 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14504 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14505 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14506 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163499 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36132 (p : Pattern) (ha : d129472 p = 1) (hb : d163510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35980 q hb ha
    | true =>
      simp only [d163505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35959 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36133 (p : Pattern) (ha : d129472 p = 1) (hb : d163516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35951 q ha hb
    | true =>
      simp only [d14508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35954 q ha hb
  have h2 (q : Pattern) (ha : d14509 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163497 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163498 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163500 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36131 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163501 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163502 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163503 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129472 q = 1) (hb : d163504 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36132 q ha hb
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163512 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129472 q = 1) (hb : d163513 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129472 q = 1) (hb : d163514 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129472 q = 1) (hb : d163515 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129472 q = 1) (hb : d163516 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36134 (p : Pattern) (ha : d129472 p = 1) (hb : d163522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163517 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36133 q ha hb
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163518 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163519 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163520 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163521 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163522 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36135 (p : Pattern) (ha : d129472 p = 1) (hb : d163527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14809 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35990 q ha hb
    | true =>
      simp only [d14809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35991 q ha hb
  have h2 (q : Pattern) (ha : d14810 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14811 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14812 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14813 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36136 (p : Pattern) (ha : d129472 p = 1) (hb : d163534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15018 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15026 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15027 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15028 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15044 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15045 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15046 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163533 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d163533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163534 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h11 p ha hb
theorem andIntro36137 (p : Pattern) (ha : d129472 p = 1) (hb : d163540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163535 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36136 q ha hb
    | true =>
      simp only [d163535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163536 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35998 q ha hb
    | true =>
      simp only [d15049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163537 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163538 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163539 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163540 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36138 (p : Pattern) (ha : d129472 p = 1) (hb : d163546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163541 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36137 q ha hb
    | true =>
      simp only [d163541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35999 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163542 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163543 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36139 (p : Pattern) (ha : d129472 p = 1) (hb : d163552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35989 q ha hb
    | true =>
      simp only [d14815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35992 q ha hb
  have h2 (q : Pattern) (ha : d14816 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163525 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163526 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36135 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163530 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163531 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129472 q = 1) (hb : d163532 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36138 q ha hb
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129472 q = 1) (hb : d163549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129472 q = 1) (hb : d163550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129472 q = 1) (hb : d163551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129472 q = 1) (hb : d163552 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36140 (p : Pattern) (ha : d129472 p = 1) (hb : d163558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163553 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36139 q ha hb
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163554 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163555 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163556 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163557 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163558 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36141 (p : Pattern) (ha : d129472 p = 1) (hb : d163564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15202 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36033 q ha hb
    | true =>
      simp only [d15202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36034 q ha hb
  have h2 (q : Pattern) (ha : d15203 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15204 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15205 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15206 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163564 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36142 (p : Pattern) (ha : d129472 p = 1) (hb : d163571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15410 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15411 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15419 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15420 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15421 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15437 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15438 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15439 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163570 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d163570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163571 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h11 p ha hb
theorem andIntro36143 (p : Pattern) (ha : d129472 p = 1) (hb : d163577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163572 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36142 q ha hb
    | true =>
      simp only [d163572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163573 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36041 q ha hb
    | true =>
      simp only [d15442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163574 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163575 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163576 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36144 (p : Pattern) (ha : d129472 p = 1) (hb : d163583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163578 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36143 q ha hb
    | true =>
      simp only [d163578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36042 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163579 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36145 (p : Pattern) (ha : d129472 p = 1) (hb : d163589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36032 q ha hb
    | true =>
      simp only [d15208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36035 q ha hb
  have h2 (q : Pattern) (ha : d15209 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163562 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163563 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163565 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36141 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163566 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163567 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163568 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129472 q = 1) (hb : d163569 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36144 q ha hb
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129472 q = 1) (hb : d163586 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129472 q = 1) (hb : d163587 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129472 q = 1) (hb : d163588 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129472 q = 1) (hb : d163589 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36146 (p : Pattern) (ha : d129472 p = 1) (hb : d163595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163590 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36145 q ha hb
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163591 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163592 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163593 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163594 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163595 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36147 (p : Pattern) (ha : d129472 p = 1) (hb : d163602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15594 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36076 q ha hb
    | true =>
      simp only [d15594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36077 q ha hb
  have h2 (q : Pattern) (ha : d15595 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15596 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15597 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15598 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro36148 (p : Pattern) (ha : d129472 p = 1) (hb : d163609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15788 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15789 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15797 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d15798 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d15799 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15815 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15816 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d129472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15817 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163608 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d163608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163609 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h11 p ha hb
theorem andIntro36149 (p : Pattern) (ha : d129472 p = 1) (hb : d163615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36148 q ha hb
    | true =>
      simp only [d163610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36084 q ha hb
    | true =>
      simp only [d15820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163612 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163613 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro36150 (p : Pattern) (ha : d129472 p = 1) (hb : d163621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36149 q ha hb
    | true =>
      simp only [d163616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36085 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36151 (p : Pattern) (ha : d129472 p = 1) (hb : d163627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36075 q ha hb
    | true =>
      simp only [d15600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36078 q ha hb
  have h2 (q : Pattern) (ha : d15601 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163600 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d163600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163601 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163603 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36147 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163604 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163605 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163606 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d129472 q = 1) (hb : d163607 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36150 q ha hb
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d129472 q = 1) (hb : d163624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d129472 q = 1) (hb : d163625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d129472 q = 1) (hb : d163626 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d129472 q = 1) (hb : d163627 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36152 (p : Pattern) (ha : d129472 p = 1) (hb : d163633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163628 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36151 q ha hb
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163629 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163631 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163632 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163633 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d163633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36153 (p : Pattern) (ha : d129472 p = 1) (hb : d163639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129472 q = 1) (hb : d163496 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36126 q ha hb
    | true =>
      simp only [d163496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36130 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163523 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36134 q ha hb
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163524 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163559 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36140 q ha hb
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163560 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163561 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129472 q = 1) (hb : d163596 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36146 q ha hb
  have h8 (q : Pattern) (ha : d129472 q = 1) (hb : d163597 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129472 q = 1) (hb : d163598 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129472 q = 1) (hb : d163599 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129472 q = 1) (hb : d163634 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36152 q ha hb
  have h12 (q : Pattern) (ha : d129472 q = 1) (hb : d163635 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129472 q = 1) (hb : d163636 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129472 q = 1) (hb : d163637 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d163637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129472 q = 1) (hb : d163638 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129472 q = 1) (hb : d163639 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d163639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro36154 (p : Pattern) (ha : d129472 p = 1) (hb : d163645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163640 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36153 q ha hb
    | true =>
      simp only [d163640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163641 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163642 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163643 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163644 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163645 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36155 (p : Pattern) (ha : d129472 p = 1) (hb : d163651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163646 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36154 q ha hb
    | true =>
      simp only [d163646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163647 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163648 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163649 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163650 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163651 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36156 (p : Pattern) (ha : d129472 p = 1) (hb : d163657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163652 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36155 q ha hb
    | true =>
      simp only [d163652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163653 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163654 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163655 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163656 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163657 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36157 (p : Pattern) (ha : d129472 p = 1) (hb : d163663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163658 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36156 q ha hb
    | true =>
      simp only [d163658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163659 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163660 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163661 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163662 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163663 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36158 (p : Pattern) (ha : d129472 p = 1) (hb : d163669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163664 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36157 q ha hb
    | true =>
      simp only [d163664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163665 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163666 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163667 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163668 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163669 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36159 (p : Pattern) (ha : d129472 p = 1) (hb : d163675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163670 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36158 q ha hb
    | true =>
      simp only [d163670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163671 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163672 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163673 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163674 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163675 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36160 (p : Pattern) (ha : d129472 p = 1) (hb : d163681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d129472 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129472 q = 1) (hb : d163676 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36159 q ha hb
    | true =>
      simp only [d163676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129472 q = 1) (hb : d163677 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129472 q = 1) (hb : d163678 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129472 q = 1) (hb : d163679 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129472 q = 1) (hb : d163680 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129472 q = 1) (hb : d163681 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro36161 (p : Pattern) (ha : d13987 p = 1) (hb : d122306 p = 1) : d123885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13982 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
    | true =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13983 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13984 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13985 q = 1) (hb : d122306 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13985, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d122306 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13986 q = 1) (hb : d122306 q = 1) : d123884 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13986, d123884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13986, d123884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13987 q = 1) (hb : d122306 q = 1) : d123885 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13987, d123885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13987, d123885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36162 (p : Pattern) (ha : d13993 p = 1) (hb : d122306 p = 1) : d123891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13991 q = 1) (hb : d122306 q = 1) : d123889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13991, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13992 q = 1) (hb : d122306 q = 1) : d123890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13992, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13993 q = 1) (hb : d122306 q = 1) : d123891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13993, d123891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13993, d123891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro36163 (p : Pattern) (ha : d122306 p = 1) (hb : d125417 p = 1) : d123897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d122306 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d122306 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13994 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36162 q ha hb
    | true =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125413 q = 1) : d123893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125413, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125413, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122306 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125414 q = 1) : d123894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125414, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125414, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125415 q = 1) : d123895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125415, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125415, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125416 q = 1) : d123896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125416, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125416, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125417 q = 1) : d123897 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125417, d123897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125417, d123897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36164 (p : Pattern) (ha : d14000 p = 1) (hb : d122306 p = 1) : d123898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13991 q = 1) (hb : d122306 q = 1) : d123889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13991, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13992 q = 1) (hb : d122306 q = 1) : d123890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13992, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13992, d123890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14000 q = 1) (hb : d122306 q = 1) : d123898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14000, d123898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14000, d123898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro36165 (p : Pattern) (ha : d122306 p = 1) (hb : d125422 p = 1) : d123904 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d122306 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d122306 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d13994 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36162 q ha hb
    | true =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125413 q = 1) : d123893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125413, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d125413, d123893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d122306 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125414 q = 1) : d123894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125414, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125414, d123894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125415 q = 1) : d123895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125415, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125415, d123895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125416 q = 1) : d123896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125416, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125416, d123896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d122306 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d122306 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d122306 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14001 q = 1) (hb : d122306 q = 1) : d123899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36164 q ha hb
    | true =>
      simp only [d14001, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125418 q = 1) : d123900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125418, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d125418, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d122306 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125419 q = 1) : d123901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125419, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125419, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125420 q = 1) : d123902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125420, d123902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d125420, d123902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122306 q = 1) (hb : d125421 q = 1) : d123903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125421, d123903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125421, d123903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d122306 q = 1) (hb : d125422 q = 1) : d123904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125422, d123904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125422, d123904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro36166 (p : Pattern) (ha : d122306 p = 1) (hb : d125429 p = 1) : d123911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d122306 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14001 q = 1) (hb : d122306 q = 1) : d123899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36164 q ha hb
    | true =>
      simp only [d14001, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125418 q = 1) : d123900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125418, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125418, d123900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d122306 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125419 q = 1) : d123901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125419, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125419, d123901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125427 q = 1) : d123909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125427, d123909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125427, d123909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125428 q = 1) : d123910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125428, d123910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125428, d123910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125429 q = 1) : d123911 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125429, d123911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125429, d123911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36167 (p : Pattern) (ha : d14026 p = 1) (hb : d122306 p = 1) : d123923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14021 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
    | true =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14022 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14023 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14024 q = 1) (hb : d122306 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14024, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d122306 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14025 q = 1) (hb : d122306 q = 1) : d123922 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14025, d123922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14025, d123922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14026 q = 1) (hb : d122306 q = 1) : d123923 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14026, d123923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14026, d123923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro36168 (p : Pattern) (ha : d14032 p = 1) (hb : d122306 p = 1) : d123929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d122306 q = 1) : d123924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36167 q ha hb
    | true =>
      simp only [d14027, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d122306 q = 1) : d123925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d122306 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14029 q = 1) (hb : d122306 q = 1) : d123926 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14029, d123926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14029, d123926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14030 q = 1) (hb : d122306 q = 1) : d123927 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14030, d123927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14030, d123927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14031 q = 1) (hb : d122306 q = 1) : d123928 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14031, d123928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14031, d123928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14032 q = 1) (hb : d122306 q = 1) : d123929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14032, d123929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14032, d123929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro36169 (p : Pattern) (ha : d122306 p = 1) (hb : d125439 p = 1) : d123935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d122306 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14033 q = 1) (hb : d122306 q = 1) : d123930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36168 q ha hb
    | true =>
      simp only [d14033, d123930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125435 q = 1) : d123931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125435, d123931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d125435, d123931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d122306 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125436 q = 1) : d123932 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125436, d123932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125436, d123932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125437 q = 1) : d123933 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125437, d123933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125437, d123933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125438 q = 1) : d123934 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125438, d123934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125438, d123934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125439 q = 1) : d123935 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125439, d123935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125439, d123935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36170 (p : Pattern) (ha : d122306 p = 1) (hb : d125445 p = 1) : d123941 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d122306 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125423 q = 1) : d123905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125423, d123905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36163 q ha hb
    | true =>
      simp only [d125423, d123905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36165 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d122306 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125424 q = 1) : d123906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125424, d123906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125424, d123906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125425 q = 1) : d123907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125425, d123907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125425, d123907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125426 q = 1) : d123908 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125426, d123908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125426, d123908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125430 q = 1) : d123912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125430, d123912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125430, d123912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36166 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125431 q = 1) : d123913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125431, d123913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125431, d123913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125432 q = 1) : d123914 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125432, d123914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125432, d123914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125433 q = 1) : d123915 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125433, d123915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125433, d123915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125434 q = 1) : d123916 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125434, d123916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125434, d123916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125440 q = 1) : d123936 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125440, d123936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125440, d123936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36169 q ha hb
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125441 q = 1) : d123937 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125441, d123937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125441, d123937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125442 q = 1) : d123938 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125442, d123938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125442, d123938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125443 q = 1) : d123939 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125443, d123939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125443, d123939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125444 q = 1) : d123940 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125444, d123940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125444, d123940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125445 q = 1) : d123941 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125445, d123941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125445, d123941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro36171 (p : Pattern) (ha : d14054 p = 1) (hb : d122306 p = 1) : d123951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13994 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36162 q ha hb
    | true =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14050 q = 1) (hb : d122306 q = 1) : d123947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14051 q = 1) (hb : d122306 q = 1) : d123948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14051, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14052 q = 1) (hb : d122306 q = 1) : d123949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14053 q = 1) (hb : d122306 q = 1) : d123950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14054 q = 1) (hb : d122306 q = 1) : d123951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14054, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14054, d123951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro36172 (p : Pattern) (ha : d14061 p = 1) (hb : d122306 p = 1) : d123958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13994 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36162 q ha hb
    | true =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14050 q = 1) (hb : d122306 q = 1) : d123947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14051 q = 1) (hb : d122306 q = 1) : d123948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14051, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14052 q = 1) (hb : d122306 q = 1) : d123949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14053 q = 1) (hb : d122306 q = 1) : d123950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d122306 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14001 q = 1) (hb : d122306 q = 1) : d123899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36164 q ha hb
    | true =>
      simp only [d14001, d123899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14057 q = 1) (hb : d122306 q = 1) : d123954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, d123954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14058 q = 1) (hb : d122306 q = 1) : d123955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14058, d123955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14059 q = 1) (hb : d122306 q = 1) : d123956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d123956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14060 q = 1) (hb : d122306 q = 1) : d123957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d123957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14061 q = 1) (hb : d122306 q = 1) : d123958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14061, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14061, d123958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36173 (p : Pattern) (ha : d14141 p = 1) (hb : d122306 p = 1) : d124019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d122306 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13994 q = 1) (hb : d122306 q = 1) : d123892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36162 q ha hb
    | true =>
      simp only [d13994, d123892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14050 q = 1) (hb : d122306 q = 1) : d123947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14050, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14050, d123947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14051 q = 1) (hb : d122306 q = 1) : d123948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14051, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14051, d123948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14052 q = 1) (hb : d122306 q = 1) : d123949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14052, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14052, d123949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14053 q = 1) (hb : d122306 q = 1) : d123950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14053, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14053, d123950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d122306 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14141 q = 1) (hb : d122306 q = 1) : d124019 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14141, d124019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14141, d124019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36174 (p : Pattern) (ha : d14066 p = 1) (hb : d122306 p = 1) : d123963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13991 q = 1) (hb : d122306 q = 1) : d123889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13991, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14065 q = 1) (hb : d122306 q = 1) : d123962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14066 q = 1) (hb : d122306 q = 1) : d123963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14066, d123963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14066, d123963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro36175 (p : Pattern) (ha : d14073 p = 1) (hb : d122306 p = 1) : d123970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14071 q = 1) (hb : d122306 q = 1) : d123968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14072 q = 1) (hb : d122306 q = 1) : d123969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14072, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14073 q = 1) (hb : d122306 q = 1) : d123970 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14073, d123970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14073, d123970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro36176 (p : Pattern) (ha : d14085 p = 1) (hb : d122306 p = 1) : d123980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14080 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34487 q ha hb
    | true =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
  have h2 (q : Pattern) (ha : d14081 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14082 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13984 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14083 q = 1) (hb : d122306 q = 1) : d123978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14083, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13982 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
    | true =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13983 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13984 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13985 q = 1) (hb : d122306 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13985, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13985, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d14084 q = 1) (hb : d122306 q = 1) : d123979 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14084, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14084, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d14085 q = 1) (hb : d122306 q = 1) : d123980 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14085, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14085, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36177 (p : Pattern) (ha : d14091 p = 1) (hb : d122306 p = 1) : d123986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36176 q ha hb
    | true =>
      simp only [d14086, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d122306 q = 1) : d123983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d122306 q = 1) : d123984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d122306 q = 1) : d123985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14091 q = 1) (hb : d122306 q = 1) : d123986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14091, d123986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14091, d123986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36178 (p : Pattern) (ha : d14112 p = 1) (hb : d122306 p = 1) : d123992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d122306 q = 1) : d123989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d122306 q = 1) : d123990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d122306 q = 1) : d123991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14112 q = 1) (hb : d122306 q = 1) : d123992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14112, d123992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14112, d123992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36179 (p : Pattern) (ha : d122306 p = 1) (hb : d125455 p = 1) : d123998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d122306 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14067 q = 1) (hb : d122306 q = 1) : d123964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36174 q ha hb
    | true =>
      simp only [d14067, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14068 q = 1) (hb : d122306 q = 1) : d123965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14069 q = 1) (hb : d122306 q = 1) : d123966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14069, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14070 q = 1) (hb : d122306 q = 1) : d123967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d122306 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14074 q = 1) (hb : d122306 q = 1) : d123971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36175 q ha hb
    | true =>
      simp only [d14074, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14075 q = 1) (hb : d122306 q = 1) : d123972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14076 q = 1) (hb : d122306 q = 1) : d123973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14076, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14092 q = 1) (hb : d122306 q = 1) : d123987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36177 q ha hb
    | true =>
      simp only [d14092, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36162 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125451 q = 1) : d123988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125451, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14113 q = 1) (hb : d122306 q = 1) : d123993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36178 q ha hb
    | true =>
      simp only [d14113, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d14114 q = 1) (hb : d122306 q = 1) : d123994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14114, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125452 q = 1) : d123995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125452, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125453 q = 1) : d123996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125453, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125454 q = 1) : d123997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125454, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125455 q = 1) : d123998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125455, d123998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125455, d123998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro36180 (p : Pattern) (ha : d14119 p = 1) (hb : d122306 p = 1) : d123999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13991 q = 1) (hb : d122306 q = 1) : d123889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13991, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13991, d123889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14065 q = 1) (hb : d122306 q = 1) : d123962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14065, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14065, d123962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14119 q = 1) (hb : d122306 q = 1) : d123999 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14119, d123999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14119, d123999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro36181 (p : Pattern) (ha : d14124 p = 1) (hb : d122306 p = 1) : d124004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d122306 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13990 q = 1) (hb : d122306 q = 1) : d123888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13990, d123888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14071 q = 1) (hb : d122306 q = 1) : d123968 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14071, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14071, d123968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14072 q = 1) (hb : d122306 q = 1) : d123969 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14072, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14072, d123969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14124 q = 1) (hb : d122306 q = 1) : d124004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14124, d124004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14124, d124004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro36182 (p : Pattern) (ha : d14128 p = 1) (hb : d122306 p = 1) : d124008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14086 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14086, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36176 q ha hb
    | true =>
      simp only [d14086, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14087 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14087, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14087, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14088 q = 1) (hb : d122306 q = 1) : d123983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14088, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14088, d123983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14089 q = 1) (hb : d122306 q = 1) : d123984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14089, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14089, d123984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14090 q = 1) (hb : d122306 q = 1) : d123985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14090, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14090, d123985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14128 q = 1) (hb : d122306 q = 1) : d124008 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14128, d124008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14128, d124008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36183 (p : Pattern) (ha : d14133 p = 1) (hb : d122306 p = 1) : d124011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13988 q = 1) (hb : d122306 q = 1) : d123886 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36161 q ha hb
    | true =>
      simp only [d13988, d123886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13989 q = 1) (hb : d122306 q = 1) : d123887 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13989, d123887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14109 q = 1) (hb : d122306 q = 1) : d123989 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14109, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14109, d123989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14110 q = 1) (hb : d122306 q = 1) : d123990 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14110, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14110, d123990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14111 q = 1) (hb : d122306 q = 1) : d123991 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14111, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14111, d123991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14133 q = 1) (hb : d122306 q = 1) : d124011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14133, d124011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14133, d124011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36184 (p : Pattern) (ha : d122306 p = 1) (hb : d125460 p = 1) : d124017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d122306 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14067 q = 1) (hb : d122306 q = 1) : d123964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14067, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36174 q ha hb
    | true =>
      simp only [d14067, d123964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14068 q = 1) (hb : d122306 q = 1) : d123965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14068, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14068, d123965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14069 q = 1) (hb : d122306 q = 1) : d123966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14069, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14069, d123966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14070 q = 1) (hb : d122306 q = 1) : d123967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14070, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14070, d123967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d122306 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14074 q = 1) (hb : d122306 q = 1) : d123971 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14074, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36175 q ha hb
    | true =>
      simp only [d14074, d123971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14075 q = 1) (hb : d122306 q = 1) : d123972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14075, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14075, d123972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14076 q = 1) (hb : d122306 q = 1) : d123973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14076, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14076, d123973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14092 q = 1) (hb : d122306 q = 1) : d123987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14092, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36177 q ha hb
    | true =>
      simp only [d14092, d123987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36162 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125451 q = 1) : d123988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125451, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d125451, d123988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d14113 q = 1) (hb : d122306 q = 1) : d123993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14113, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36178 q ha hb
    | true =>
      simp only [d14113, d123993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d14114 q = 1) (hb : d122306 q = 1) : d123994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14114, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14114, d123994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125452 q = 1) : d123995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125452, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125452, d123995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125453 q = 1) : d123996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125453, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d125453, d123996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125454 q = 1) : d123997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125454, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125454, d123997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d122306 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d14120 q = 1) (hb : d122306 q = 1) : d124000 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14120, d124000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36180 q ha hb
    | true =>
      simp only [d14120, d124000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14121 q = 1) (hb : d122306 q = 1) : d124001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14121, d124001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14121, d124001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14122 q = 1) (hb : d122306 q = 1) : d124002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14122, d124002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d14122, d124002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d14123 q = 1) (hb : d122306 q = 1) : d124003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14123, d124003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14123, d124003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d122306 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d14125 q = 1) (hb : d122306 q = 1) : d124005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14125, d124005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36181 q ha hb
    | true =>
      simp only [d14125, d124005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d14126 q = 1) (hb : d122306 q = 1) : d124006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14126, d124006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14126, d124006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d14127 q = 1) (hb : d122306 q = 1) : d124007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14127, d124007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14127, d124007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d14129 q = 1) (hb : d122306 q = 1) : d124009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36182 q ha hb
    | true =>
      simp only [d14129, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36164 q ha hb
  have h27 (q : Pattern) (ha : d122306 q = 1) (hb : d125456 q = 1) : d124010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d125456, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d14134 q = 1) (hb : d122306 q = 1) : d124012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36183 q ha hb
    | true =>
      simp only [d14134, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d14135 q = 1) (hb : d122306 q = 1) : d124013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d14135, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d122306 q = 1) (hb : d125457 q = 1) : d124014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d125457, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d122306 q = 1) (hb : d125458 q = 1) : d124015 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125458, d124015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d125458, d124015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d122306 q = 1) (hb : d125459 q = 1) : d124016 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125459, d124016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125459, d124016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d122306 q = 1) (hb : d125460 q = 1) : d124017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125460, d124017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125460, d124017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro36185 (p : Pattern) (ha : d122306 p = 1) (hb : d125467 p = 1) : d124026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14129 q = 1) (hb : d122306 q = 1) : d124009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14129, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36182 q ha hb
    | true =>
      simp only [d14129, d124009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36164 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125456 q = 1) : d124010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125456, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125456, d124010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14134 q = 1) (hb : d122306 q = 1) : d124012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14134, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36183 q ha hb
    | true =>
      simp only [d14134, d124012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14135 q = 1) (hb : d122306 q = 1) : d124013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14135, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14135, d124013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125457 q = 1) : d124014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125457, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125457, d124014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125465 q = 1) : d124024 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125465, d124024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125465, d124024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125466 q = 1) : d124025 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125466, d124025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125466, d124025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125467 q = 1) : d124026 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125467, d124026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125467, d124026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36186 (p : Pattern) (ha : d14162 p = 1) (hb : d122306 p = 1) : d124038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14157 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34498 q ha hb
    | true =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
  have h2 (q : Pattern) (ha : d14158 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14159 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14023 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14160 q = 1) (hb : d122306 q = 1) : d124036 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14160, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14021 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
    | true =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14022 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14023 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14024 q = 1) (hb : d122306 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14024, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14024, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d14161 q = 1) (hb : d122306 q = 1) : d124037 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14161, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14161, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d14162 q = 1) (hb : d122306 q = 1) : d124038 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14162, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14162, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36187 (p : Pattern) (ha : d14168 p = 1) (hb : d122306 p = 1) : d124044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14163 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14163, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36186 q ha hb
    | true =>
      simp only [d14163, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14164 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14164, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14164, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14027 q = 1) (hb : d122306 q = 1) : d123924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36167 q ha hb
    | true =>
      simp only [d14027, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14028 q = 1) (hb : d122306 q = 1) : d123925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14165 q = 1) (hb : d122306 q = 1) : d124041 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14165, d124041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14165, d124041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14166 q = 1) (hb : d122306 q = 1) : d124042 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14166, d124042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14166, d124042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14167 q = 1) (hb : d122306 q = 1) : d124043 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14167, d124043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14167, d124043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14168 q = 1) (hb : d122306 q = 1) : d124044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14168, d124044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14168, d124044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36188 (p : Pattern) (ha : d14189 p = 1) (hb : d122306 p = 1) : d124050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14027 q = 1) (hb : d122306 q = 1) : d123924 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14027, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36167 q ha hb
    | true =>
      simp only [d14027, d123924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14028 q = 1) (hb : d122306 q = 1) : d123925 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14028, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14028, d123925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14186 q = 1) (hb : d122306 q = 1) : d124047 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14186, d124047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14186, d124047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14187 q = 1) (hb : d122306 q = 1) : d124048 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14187, d124048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14187, d124048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14188 q = 1) (hb : d122306 q = 1) : d124049 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14188, d124049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14188, d124049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14189 q = 1) (hb : d122306 q = 1) : d124050 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14189, d124050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14189, d124050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36189 (p : Pattern) (ha : d122306 p = 1) (hb : d125477 p = 1) : d124056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14169 q = 1) (hb : d122306 q = 1) : d124045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14169, d124045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36187 q ha hb
    | true =>
      simp only [d14169, d124045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36168 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125473 q = 1) : d124046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125473, d124046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125473, d124046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14190 q = 1) (hb : d122306 q = 1) : d124051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14190, d124051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36188 q ha hb
    | true =>
      simp only [d14190, d124051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14191 q = 1) (hb : d122306 q = 1) : d124052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14191, d124052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14191, d124052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125474 q = 1) : d124053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125474, d124053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125474, d124053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125475 q = 1) : d124054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125475, d124054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125475, d124054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125476 q = 1) : d124055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125476, d124055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125476, d124055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125477 q = 1) : d124056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125477, d124056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125477, d124056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36190 (p : Pattern) (ha : d122306 p = 1) (hb : d125483 p = 1) : d124062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14055 q = 1) (hb : d122306 q = 1) : d123952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14055, d123952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14055, d123952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36171 q ha hb
  have h2 (q : Pattern) (ha : d14056 q = 1) (hb : d122306 q = 1) : d123953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14056, d123953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14056, d123953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14062 q = 1) (hb : d122306 q = 1) : d123959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36171 q ha hb
    | true =>
      simp only [d14062, d123959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36172 q ha hb
  have h4 (q : Pattern) (ha : d14063 q = 1) (hb : d122306 q = 1) : d123960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14063, d123960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14064 q = 1) (hb : d122306 q = 1) : d123961 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14064, d123961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14064, d123961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125461 q = 1) : d124018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125461, d124018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36179 q ha hb
    | true =>
      simp only [d125461, d124018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36184 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d122306 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14142 q = 1) (hb : d122306 q = 1) : d124020 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14142, d124020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36173 q ha hb
    | true =>
      simp only [d14142, d124020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125462 q = 1) : d124021 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125462, d124021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125462, d124021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125463 q = 1) : d124022 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125463, d124022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125463, d124022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125464 q = 1) : d124023 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125464, d124023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125464, d124023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125468 q = 1) : d124027 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125468, d124027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125468, d124027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36185 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d122306 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125469 q = 1) : d124028 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125469, d124028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d125469, d124028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125470 q = 1) : d124029 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125470, d124029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125470, d124029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125471 q = 1) : d124030 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125471, d124030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125471, d124030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125472 q = 1) : d124031 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125472, d124031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125472, d124031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d122306 q = 1) (hb : d125478 q = 1) : d124057 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125478, d124057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125478, d124057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36189 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d122306 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d122306 q = 1) (hb : d125479 q = 1) : d124058 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125479, d124058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125479, d124058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d122306 q = 1) (hb : d125480 q = 1) : d124059 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125480, d124059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125480, d124059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122306 q = 1) (hb : d125481 q = 1) : d124060 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125481, d124060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125481, d124060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125482 q = 1) : d124061 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125482, d124061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125482, d124061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d122306 q = 1) (hb : d125483 q = 1) : d124062 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125483, d124062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125483, d124062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro36191 (p : Pattern) (ha : d122306 p = 1) (hb : d125489 p = 1) : d124068 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d122306 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125446 q = 1) : d123942 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125446, d123942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125446, d123942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36170 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125447 q = 1) : d123943 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125447, d123943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125447, d123943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125448 q = 1) : d123944 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125448, d123944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125448, d123944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125449 q = 1) : d123945 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125449, d123945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125449, d123945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125450 q = 1) : d123946 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125450, d123946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125450, d123946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125484 q = 1) : d124063 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125484, d124063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125484, d124063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36190 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125485 q = 1) : d124064 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125485, d124064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125485, d124064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125486 q = 1) : d124065 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125486, d124065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125486, d124065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125487 q = 1) : d124066 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125487, d124066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125487, d124066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125488 q = 1) : d124067 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125488, d124067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125488, d124067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125489 q = 1) : d124068 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125489, d124068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125489, d124068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro36192 (p : Pattern) (ha : d14210 p = 1) (hb : d122306 p = 1) : d123980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14080 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34487 q ha hb
    | true =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
  have h2 (q : Pattern) (ha : d14081 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14082 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13984 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14083 q = 1) (hb : d122306 q = 1) : d123978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14083, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13982 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
    | true =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13983 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13984 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14208 q = 1) (hb : d122306 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14208, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14209 q = 1) (hb : d122306 q = 1) : d123979 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14209, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14209, d123979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d14210 q = 1) (hb : d122306 q = 1) : d123980 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14210, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14210, d123980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36193 (p : Pattern) (ha : d14214 p = 1) (hb : d122306 p = 1) : d124070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d122305 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13982 q = 1) (hb : d122305 q = 1) : d123880 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
    | true =>
      simp only [d13982, d123880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13983 q = 1) (hb : d122305 q = 1) : d123881 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13983, d123881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13984 q = 1) (hb : d122305 q = 1) : d123882 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13984, d123882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14208 q = 1) (hb : d122306 q = 1) : d123883 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14208, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14208, d122306, d123883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14213 q = 1) (hb : d122306 q = 1) : d124069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14213, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14213, d124069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14214 q = 1) (hb : d122306 q = 1) : d124070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14214, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14214, d124070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro36194 (p : Pattern) (ha : d14220 p = 1) (hb : d122306 p = 1) : d124076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14219 q = 1) (hb : d122306 q = 1) : d124075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14219, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14220 q = 1) (hb : d122306 q = 1) : d124076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14220, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14220, d124076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36195 (p : Pattern) (ha : d14224 p = 1) (hb : d122306 p = 1) : d124080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d122306 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14223 q = 1) (hb : d122306 q = 1) : d124079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14223, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14224 q = 1) (hb : d122306 q = 1) : d124080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14224, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14224, d124080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36196 (p : Pattern) (ha : d14230 p = 1) (hb : d122306 p = 1) : d124086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d122306 q = 1) : d124081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36194 q ha hb
    | true =>
      simp only [d14225, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36195 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d122306 q = 1) : d124082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d122306 q = 1) : d124083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d122306 q = 1) : d124084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d122306 q = 1) : d124085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14230 q = 1) (hb : d122306 q = 1) : d124086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14230, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14230, d124086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36197 (p : Pattern) (ha : d14233 p = 1) (hb : d122306 p = 1) : d124089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14219 q = 1) (hb : d122306 q = 1) : d124075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14219, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14219, d124075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14233 q = 1) (hb : d122306 q = 1) : d124089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14233, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14233, d124089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36198 (p : Pattern) (ha : d14234 p = 1) (hb : d122306 p = 1) : d124090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d122306 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14223 q = 1) (hb : d122306 q = 1) : d124079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14223, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14223, d124079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14234 q = 1) (hb : d122306 q = 1) : d124090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14234, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14234, d124090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36199 (p : Pattern) (ha : d14240 p = 1) (hb : d122306 p = 1) : d124096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d122306 q = 1) : d124081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36194 q ha hb
    | true =>
      simp only [d14225, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36195 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d122306 q = 1) : d124082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d122306 q = 1) : d124083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d122306 q = 1) : d124084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d122306 q = 1) : d124085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14235 q = 1) (hb : d122306 q = 1) : d124091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36197 q ha hb
    | true =>
      simp only [d14235, d124091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36198 q ha hb
  have h7 (q : Pattern) (ha : d14236 q = 1) (hb : d122306 q = 1) : d124092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, d124092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14237 q = 1) (hb : d122306 q = 1) : d124093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14237, d124093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14238 q = 1) (hb : d122306 q = 1) : d124094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d124094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14239 q = 1) (hb : d122306 q = 1) : d124095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d124095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14240 q = 1) (hb : d122306 q = 1) : d124096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14240, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14240, d124096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36200 (p : Pattern) (ha : d14349 p = 1) (hb : d122306 p = 1) : d124169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14225 q = 1) (hb : d122306 q = 1) : d124081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14225, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36194 q ha hb
    | true =>
      simp only [d14225, d124081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36195 q ha hb
  have h2 (q : Pattern) (ha : d14226 q = 1) (hb : d122306 q = 1) : d124082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14226, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14226, d124082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14227 q = 1) (hb : d122306 q = 1) : d124083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14227, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14227, d124083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14228 q = 1) (hb : d122306 q = 1) : d124084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14228, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14228, d124084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14229 q = 1) (hb : d122306 q = 1) : d124085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14229, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14229, d124085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14344 q = 1) (hb : d122306 q = 1) : d124164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36195 q ha hb
    | true =>
      simp only [d14344, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14345 q = 1) (hb : d122306 q = 1) : d124165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14345, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14346 q = 1) (hb : d122306 q = 1) : d124166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14346, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14347 q = 1) (hb : d122306 q = 1) : d124167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14347, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14348 q = 1) (hb : d122306 q = 1) : d124168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14348, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14349 q = 1) (hb : d122306 q = 1) : d124169 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14349, d124169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14349, d124169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36201 (p : Pattern) (ha : d14355 p = 1) (hb : d122306 p = 1) : d124175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14344 q = 1) (hb : d122306 q = 1) : d124164 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14344, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36195 q ha hb
    | true =>
      simp only [d14344, d124164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14345 q = 1) (hb : d122306 q = 1) : d124165 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14345, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14345, d124165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14346 q = 1) (hb : d122306 q = 1) : d124166 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14346, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14346, d124166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14347 q = 1) (hb : d122306 q = 1) : d124167 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14347, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14347, d124167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14348 q = 1) (hb : d122306 q = 1) : d124168 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14348, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14348, d124168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14350 q = 1) (hb : d122306 q = 1) : d124170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36198 q ha hb
    | true =>
      simp only [d14350, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14351 q = 1) (hb : d122306 q = 1) : d124171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14351, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14352 q = 1) (hb : d122306 q = 1) : d124172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14352, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14353 q = 1) (hb : d122306 q = 1) : d124173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14353, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14354 q = 1) (hb : d122306 q = 1) : d124174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14354, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14355 q = 1) (hb : d122306 q = 1) : d124175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14355, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14355, d124175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36202 (p : Pattern) (ha : d14364 p = 1) (hb : d122306 p = 1) : d124184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14350 q = 1) (hb : d122306 q = 1) : d124170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14350, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36198 q ha hb
    | true =>
      simp only [d14350, d124170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14351 q = 1) (hb : d122306 q = 1) : d124171 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14351, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14351, d124171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14352 q = 1) (hb : d122306 q = 1) : d124172 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14352, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14352, d124172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14353 q = 1) (hb : d122306 q = 1) : d124173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14353, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14353, d124173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14354 q = 1) (hb : d122306 q = 1) : d124174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14354, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14354, d124174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14364 q = 1) (hb : d122306 q = 1) : d124184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14364, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14364, d124184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36203 (p : Pattern) (ha : d14395 p = 1) (hb : d122306 p = 1) : d124204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14021 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
    | true =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14022 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14023 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14385 q = 1) (hb : d122306 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14385, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14394 q = 1) (hb : d122306 q = 1) : d124203 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14394, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14394, d124203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14395 q = 1) (hb : d122306 q = 1) : d124204 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14395, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14395, d124204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro36204 (p : Pattern) (ha : d14447 p = 1) (hb : d122306 p = 1) : d124227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14396 q = 1) (hb : d122306 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36203 q ha hb
    | true =>
      simp only [d14396, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14397 q = 1) (hb : d122306 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14397, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14444 q = 1) (hb : d122306 q = 1) : d124224 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14444, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14444, d124224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14445 q = 1) (hb : d122306 q = 1) : d124225 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14445, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14445, d124225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14446 q = 1) (hb : d122306 q = 1) : d124226 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14446, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14446, d124226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14447 q = 1) (hb : d122306 q = 1) : d124227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14447, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14447, d124227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36205 (p : Pattern) (ha : d14453 p = 1) (hb : d122306 p = 1) : d124233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14448 q = 1) (hb : d122306 q = 1) : d124228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14448, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36204 q ha hb
    | true =>
      simp only [d14448, d124228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14449 q = 1) (hb : d122306 q = 1) : d124229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14449, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14449, d124229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14450 q = 1) (hb : d122306 q = 1) : d124230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14450, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14450, d124230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14451 q = 1) (hb : d122306 q = 1) : d124231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14451, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14451, d124231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14452 q = 1) (hb : d122306 q = 1) : d124232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14452, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14452, d124232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14453 q = 1) (hb : d122306 q = 1) : d124233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14453, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14453, d124233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36206 (p : Pattern) (ha : d14245 p = 1) (hb : d122306 p = 1) : d124101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14244 q = 1) (hb : d122306 q = 1) : d124100 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14244, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14245 q = 1) (hb : d122306 q = 1) : d124101 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14245, d124101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14245, d124101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36207 (p : Pattern) (ha : d14247 p = 1) (hb : d122306 p = 1) : d124103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d122306 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14246 q = 1) (hb : d122306 q = 1) : d124102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14246, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14247 q = 1) (hb : d122306 q = 1) : d124103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14247, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14247, d124103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36208 (p : Pattern) (ha : d14254 p = 1) (hb : d122306 p = 1) : d124110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14252 q = 1) (hb : d122306 q = 1) : d124108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14252, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14253 q = 1) (hb : d122306 q = 1) : d124109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14253, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14254 q = 1) (hb : d122306 q = 1) : d124110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14254, d124110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14254, d124110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36209 (p : Pattern) (ha : d14257 p = 1) (hb : d122306 p = 1) : d124113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14255 q = 1) (hb : d122306 q = 1) : d124111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14255, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14256 q = 1) (hb : d122306 q = 1) : d124112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14256, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14257 q = 1) (hb : d122306 q = 1) : d124113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14257, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14257, d124113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36210 (p : Pattern) (ha : d14273 p = 1) (hb : d122306 p = 1) : d124123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14264 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14264, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
    | true =>
      simp only [d14264, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34487 q ha hb
  have h2 (q : Pattern) (ha : d14265 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14265, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14265, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14266 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14266, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14266, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14270 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14271 q = 1) (hb : d122306 q = 1) : d124121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14271, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14271, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14080 q = 1) (hb : d122305 q = 1) : d123975 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34487 q ha hb
    | true =>
      simp only [d14080, d123975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34470 q ha hb
  have h7 (q : Pattern) (ha : d14081 q = 1) (hb : d122305 q = 1) : d123976 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14081, d123976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14082 q = 1) (hb : d122305 q = 1) : d123977 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14082, d123977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13984 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14083 q = 1) (hb : d122306 q = 1) : d123978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14083, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14083, d122306, d123978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14272 q = 1) (hb : d122306 q = 1) : d124122 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14272, d124122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14272, d124122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14273 q = 1) (hb : d122306 q = 1) : d124123 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14273, d124123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14273, d124123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36211 (p : Pattern) (ha : d14279 p = 1) (hb : d122306 p = 1) : d124129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14274 q = 1) (hb : d122306 q = 1) : d124124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36210 q ha hb
    | true =>
      simp only [d14274, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14275 q = 1) (hb : d122306 q = 1) : d124125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14275, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14276 q = 1) (hb : d122306 q = 1) : d124126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14276, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14277 q = 1) (hb : d122306 q = 1) : d124127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14277, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14278 q = 1) (hb : d122306 q = 1) : d124128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14278, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14279 q = 1) (hb : d122306 q = 1) : d124129 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14279, d124129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14279, d124129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36212 (p : Pattern) (ha : d14312 p = 1) (hb : d122306 p = 1) : d124135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14309 q = 1) (hb : d122306 q = 1) : d124132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14309, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14310 q = 1) (hb : d122306 q = 1) : d124133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14310, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14311 q = 1) (hb : d122306 q = 1) : d124134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14311, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14312 q = 1) (hb : d122306 q = 1) : d124135 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14312, d124135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14312, d124135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36213 (p : Pattern) (ha : d122306 p = 1) (hb : d125494 p = 1) : d124141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14248 q = 1) (hb : d122306 q = 1) : d124104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36206 q ha hb
    | true =>
      simp only [d14248, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36207 q ha hb
  have h2 (q : Pattern) (ha : d14249 q = 1) (hb : d122306 q = 1) : d124105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14249, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14250 q = 1) (hb : d122306 q = 1) : d124106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14250, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14251 q = 1) (hb : d122306 q = 1) : d124107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14251, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14258 q = 1) (hb : d122306 q = 1) : d124114 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36208 q ha hb
    | true =>
      simp only [d14258, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36209 q ha hb
  have h6 (q : Pattern) (ha : d14259 q = 1) (hb : d122306 q = 1) : d124115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14259, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14260 q = 1) (hb : d122306 q = 1) : d124116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14260, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14280 q = 1) (hb : d122306 q = 1) : d124130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36211 q ha hb
    | true =>
      simp only [d14280, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36194 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125490 q = 1) : d124131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125490, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14313 q = 1) (hb : d122306 q = 1) : d124136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36212 q ha hb
    | true =>
      simp only [d14313, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14314 q = 1) (hb : d122306 q = 1) : d124137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14314, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125491 q = 1) : d124138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125491, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125492 q = 1) : d124139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125492, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125493 q = 1) : d124140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125493, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125494 q = 1) : d124141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125494, d124141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125494, d124141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro36214 (p : Pattern) (ha : d14319 p = 1) (hb : d122306 p = 1) : d124142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14218 q = 1) (hb : d122306 q = 1) : d124074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14218, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14218, d124074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14244 q = 1) (hb : d122306 q = 1) : d124100 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14244, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14244, d124100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14319 q = 1) (hb : d122306 q = 1) : d124142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14319, d124142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14319, d124142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36215 (p : Pattern) (ha : d14320 p = 1) (hb : d122306 p = 1) : d124143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14222 q = 1) (hb : d122306 q = 1) : d124078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14222, d124078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14246 q = 1) (hb : d122306 q = 1) : d124102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14246, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14246, d124102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14320 q = 1) (hb : d122306 q = 1) : d124143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14320, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14320, d124143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36216 (p : Pattern) (ha : d14325 p = 1) (hb : d122306 p = 1) : d124148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14217 q = 1) (hb : d122306 q = 1) : d124073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14217, d124073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14252 q = 1) (hb : d122306 q = 1) : d124108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14252, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14252, d124108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14253 q = 1) (hb : d122306 q = 1) : d124109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14253, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14253, d124109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14325 q = 1) (hb : d122306 q = 1) : d124148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14325, d124148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14325, d124148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36217 (p : Pattern) (ha : d14326 p = 1) (hb : d122306 p = 1) : d124149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14215 q = 1) (hb : d122306 q = 1) : d124071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36193 q ha hb
    | true =>
      simp only [d14215, d124071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14216 q = 1) (hb : d122306 q = 1) : d124072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14216, d124072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14221 q = 1) (hb : d122306 q = 1) : d124077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14221, d124077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14255 q = 1) (hb : d122306 q = 1) : d124111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14255, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14255, d124111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14256 q = 1) (hb : d122306 q = 1) : d124112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14256, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14256, d124112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14326 q = 1) (hb : d122306 q = 1) : d124149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14326, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14326, d124149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36218 (p : Pattern) (ha : d14330 p = 1) (hb : d122306 p = 1) : d124153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14274 q = 1) (hb : d122306 q = 1) : d124124 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14274, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36210 q ha hb
    | true =>
      simp only [d14274, d124124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14275 q = 1) (hb : d122306 q = 1) : d124125 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14275, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14275, d124125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14276 q = 1) (hb : d122306 q = 1) : d124126 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14276, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14276, d124126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14277 q = 1) (hb : d122306 q = 1) : d124127 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14277, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14277, d124127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14278 q = 1) (hb : d122306 q = 1) : d124128 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14278, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14278, d124128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14330 q = 1) (hb : d122306 q = 1) : d124153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14330, d124153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14330, d124153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36219 (p : Pattern) (ha : d14336 p = 1) (hb : d122306 p = 1) : d124156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14211 q = 1) (hb : d122306 q = 1) : d123981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36192 q ha hb
    | true =>
      simp only [d14211, d123981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14212 q = 1) (hb : d122306 q = 1) : d123982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14212, d123982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14309 q = 1) (hb : d122306 q = 1) : d124132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14309, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14309, d124132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14310 q = 1) (hb : d122306 q = 1) : d124133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14310, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14310, d124133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14311 q = 1) (hb : d122306 q = 1) : d124134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14311, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14311, d124134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14336 q = 1) (hb : d122306 q = 1) : d124156 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14336, d124156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14336, d124156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36220 (p : Pattern) (ha : d122306 p = 1) (hb : d125499 p = 1) : d124162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14248 q = 1) (hb : d122306 q = 1) : d124104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14248, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36206 q ha hb
    | true =>
      simp only [d14248, d124104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36207 q ha hb
  have h2 (q : Pattern) (ha : d14249 q = 1) (hb : d122306 q = 1) : d124105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14249, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14249, d124105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14250 q = 1) (hb : d122306 q = 1) : d124106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14250, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14250, d124106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14251 q = 1) (hb : d122306 q = 1) : d124107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14251, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14251, d124107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14258 q = 1) (hb : d122306 q = 1) : d124114 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14258, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36208 q ha hb
    | true =>
      simp only [d14258, d124114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36209 q ha hb
  have h6 (q : Pattern) (ha : d14259 q = 1) (hb : d122306 q = 1) : d124115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14259, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14259, d124115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14260 q = 1) (hb : d122306 q = 1) : d124116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14260, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14260, d124116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14280 q = 1) (hb : d122306 q = 1) : d124130 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14280, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36211 q ha hb
    | true =>
      simp only [d14280, d124130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36194 q ha hb
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125490 q = 1) : d124131 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125490, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d125490, d124131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d14313 q = 1) (hb : d122306 q = 1) : d124136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14313, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36212 q ha hb
    | true =>
      simp only [d14313, d124136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14314 q = 1) (hb : d122306 q = 1) : d124137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14314, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14314, d124137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d122306 q = 1) (hb : d125491 q = 1) : d124138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125491, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125491, d124138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125492 q = 1) : d124139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125492, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d125492, d124139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125493 q = 1) : d124140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125493, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d125493, d124140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14321 q = 1) (hb : d122306 q = 1) : d124144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14321, d124144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36214 q ha hb
    | true =>
      simp only [d14321, d124144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36215 q ha hb
  have h16 (q : Pattern) (ha : d14322 q = 1) (hb : d122306 q = 1) : d124145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14322, d124145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14322, d124145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14323 q = 1) (hb : d122306 q = 1) : d124146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14323, d124146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14323, d124146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14324 q = 1) (hb : d122306 q = 1) : d124147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14324, d124147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14324, d124147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14327 q = 1) (hb : d122306 q = 1) : d124150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14327, d124150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36216 q ha hb
    | true =>
      simp only [d14327, d124150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36217 q ha hb
  have h20 (q : Pattern) (ha : d14328 q = 1) (hb : d122306 q = 1) : d124151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14328, d124151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14328, d124151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14329 q = 1) (hb : d122306 q = 1) : d124152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14329, d124152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14329, d124152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14331 q = 1) (hb : d122306 q = 1) : d124154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36218 q ha hb
    | true =>
      simp only [d14331, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36197 q ha hb
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125495 q = 1) : d124155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d125495, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d14337 q = 1) (hb : d122306 q = 1) : d124157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36219 q ha hb
    | true =>
      simp only [d14337, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14338 q = 1) (hb : d122306 q = 1) : d124158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14338, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d122306 q = 1) (hb : d125496 q = 1) : d124159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125496, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d122306 q = 1) (hb : d125497 q = 1) : d124160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125497, d124160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d125497, d124160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d122306 q = 1) (hb : d125498 q = 1) : d124161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125498, d124161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d125498, d124161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d122306 q = 1) (hb : d125499 q = 1) : d124162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125499, d124162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125499, d124162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro36221 (p : Pattern) (ha : d122306 p = 1) (hb : d125506 p = 1) : d124182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14331 q = 1) (hb : d122306 q = 1) : d124154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14331, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36218 q ha hb
    | true =>
      simp only [d14331, d124154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36197 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125495 q = 1) : d124155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125495, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125495, d124155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14337 q = 1) (hb : d122306 q = 1) : d124157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14337, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36219 q ha hb
    | true =>
      simp only [d14337, d124157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14338 q = 1) (hb : d122306 q = 1) : d124158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14338, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14338, d124158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125496 q = 1) : d124159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125496, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125496, d124159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125504 q = 1) : d124180 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125504, d124180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125504, d124180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125505 q = 1) : d124181 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125505, d124181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125505, d124181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125506 q = 1) : d124182 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125506, d124182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125506, d124182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36222 (p : Pattern) (ha : d14382 p = 1) (hb : d122306 p = 1) : d124196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14373 q = 1) (hb : d122305 q = 1) : d124191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14373, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34537 q ha hb
    | true =>
      simp only [d14373, d124191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34498 q ha hb
  have h2 (q : Pattern) (ha : d14374 q = 1) (hb : d122305 q = 1) : d124192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14374, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14374, d124192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14375 q = 1) (hb : d122305 q = 1) : d124193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14375, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14375, d124193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14380 q = 1) (hb : d122306 q = 1) : d124194 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14380, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14380, d122306, d124194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14157 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34498 q ha hb
    | true =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
  have h7 (q : Pattern) (ha : d14158 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14159 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14023 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14160 q = 1) (hb : d122306 q = 1) : d124036 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14160, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14381 q = 1) (hb : d122306 q = 1) : d124195 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14381, d124195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14381, d124195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14382 q = 1) (hb : d122306 q = 1) : d124196 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14382, d124196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14382, d124196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36223 (p : Pattern) (ha : d14387 p = 1) (hb : d122306 p = 1) : d124038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14157 q = 1) (hb : d122305 q = 1) : d124033 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34498 q ha hb
    | true =>
      simp only [d14157, d124033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
  have h2 (q : Pattern) (ha : d14158 q = 1) (hb : d122305 q = 1) : d124034 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14158, d124034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14159 q = 1) (hb : d122305 q = 1) : d124035 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14159, d124035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14023 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14160 q = 1) (hb : d122306 q = 1) : d124036 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14160, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14160, d122306, d124036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d71 q = 1) (hb : d122305 q = 1) : d71 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14021 q = 1) (hb : d122305 q = 1) : d123918 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34477 q ha hb
    | true =>
      simp only [d14021, d123918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14022 q = 1) (hb : d122305 q = 1) : d123919 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14022, d123919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14023 q = 1) (hb : d122305 q = 1) : d123920 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14023, d123920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14385 q = 1) (hb : d122306 q = 1) : d123921 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14385, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14385, d122306, d123921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14386 q = 1) (hb : d122306 q = 1) : d124037 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14386, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14386, d124037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d14387 q = 1) (hb : d122306 q = 1) : d124038 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14387, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14387, d124038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36224 (p : Pattern) (ha : d14393 p = 1) (hb : d122306 p = 1) : d124202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14383 q = 1) (hb : d122306 q = 1) : d124197 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14383, d124197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36222 q ha hb
    | true =>
      simp only [d14383, d124197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14384 q = 1) (hb : d122306 q = 1) : d124198 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14384, d124198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14384, d124198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14388 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36223 q ha hb
    | true =>
      simp only [d14388, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14389 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14390 q = 1) (hb : d122306 q = 1) : d124199 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14390, d124199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14390, d124199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14391 q = 1) (hb : d122306 q = 1) : d124200 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14391, d124200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14391, d124200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14392 q = 1) (hb : d122306 q = 1) : d124201 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14392, d124201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14392, d124201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14393 q = 1) (hb : d122306 q = 1) : d124202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14393, d124202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14393, d124202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36225 (p : Pattern) (ha : d14401 p = 1) (hb : d122306 p = 1) : d124210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14388 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36223 q ha hb
    | true =>
      simp only [d14388, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14389 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14396 q = 1) (hb : d122306 q = 1) : d124205 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14396, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36203 q ha hb
    | true =>
      simp only [d14396, d124205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14397 q = 1) (hb : d122306 q = 1) : d124206 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14397, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14397, d124206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14398 q = 1) (hb : d122306 q = 1) : d124207 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14398, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14398, d124207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14399 q = 1) (hb : d122306 q = 1) : d124208 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14399, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14399, d124208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14400 q = 1) (hb : d122306 q = 1) : d124209 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14400, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14400, d124209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14401 q = 1) (hb : d122306 q = 1) : d124210 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14401, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14401, d124210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36226 (p : Pattern) (ha : d14436 p = 1) (hb : d122306 p = 1) : d124216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14388 q = 1) (hb : d122306 q = 1) : d124039 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14388, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36223 q ha hb
    | true =>
      simp only [d14388, d124039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14389 q = 1) (hb : d122306 q = 1) : d124040 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14389, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14389, d124040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14433 q = 1) (hb : d122306 q = 1) : d124213 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14433, d124213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14433, d124213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14434 q = 1) (hb : d122306 q = 1) : d124214 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14434, d124214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14434, d124214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14435 q = 1) (hb : d122306 q = 1) : d124215 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14435, d124215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14435, d124215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14436 q = 1) (hb : d122306 q = 1) : d124216 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14436, d124216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14436, d124216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36227 (p : Pattern) (ha : d122306 p = 1) (hb : d125516 p = 1) : d124222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14402 q = 1) (hb : d122306 q = 1) : d124211 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14402, d124211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36224 q ha hb
    | true =>
      simp only [d14402, d124211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36225 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125512 q = 1) : d124212 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125512, d124212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d125512, d124212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d14437 q = 1) (hb : d122306 q = 1) : d124217 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14437, d124217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36226 q ha hb
    | true =>
      simp only [d14437, d124217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14438 q = 1) (hb : d122306 q = 1) : d124218 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14438, d124218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14438, d124218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125513 q = 1) : d124219 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125513, d124219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125513, d124219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125514 q = 1) : d124220 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125514, d124220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125514, d124220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d122306 q = 1) (hb : d125515 q = 1) : d124221 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125515, d124221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125515, d124221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125516 q = 1) : d124222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125516, d124222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125516, d124222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36228 (p : Pattern) (ha : d122306 p = 1) (hb : d125522 p = 1) : d124239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14231 q = 1) (hb : d122306 q = 1) : d124087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14231, d124087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14231, d124087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36196 q ha hb
  have h2 (q : Pattern) (ha : d14232 q = 1) (hb : d122306 q = 1) : d124088 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14232, d124088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14232, d124088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14241 q = 1) (hb : d122306 q = 1) : d124097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36196 q ha hb
    | true =>
      simp only [d14241, d124097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36199 q ha hb
  have h4 (q : Pattern) (ha : d14242 q = 1) (hb : d122306 q = 1) : d124098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14242, d124098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14243 q = 1) (hb : d122306 q = 1) : d124099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14243, d124099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14243, d124099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125500 q = 1) : d124163 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125500, d124163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36213 q ha hb
    | true =>
      simp only [d125500, d124163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36220 q ha hb
  have h7 (q : Pattern) (ha : d14356 q = 1) (hb : d122306 q = 1) : d124176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14356, d124176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36200 q ha hb
    | true =>
      simp only [d14356, d124176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36201 q ha hb
  have h8 (q : Pattern) (ha : d122306 q = 1) (hb : d125501 q = 1) : d124177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125501, d124177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125501, d124177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d122306 q = 1) (hb : d125502 q = 1) : d124178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125502, d124178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125502, d124178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d122306 q = 1) (hb : d125503 q = 1) : d124179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125503, d124179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d125503, d124179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d122306 q = 1) (hb : d125507 q = 1) : d124183 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125507, d124183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125507, d124183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36221 q ha hb
  have h12 (q : Pattern) (ha : d14365 q = 1) (hb : d122306 q = 1) : d124185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14365, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14365, d124185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36202 q ha hb
  have h13 (q : Pattern) (ha : d122306 q = 1) (hb : d125508 q = 1) : d124186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125508, d124186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125508, d124186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d122306 q = 1) (hb : d125509 q = 1) : d124187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125509, d124187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125509, d124187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d122306 q = 1) (hb : d125510 q = 1) : d124188 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125510, d124188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125510, d124188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d122306 q = 1) (hb : d125511 q = 1) : d124189 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125511, d124189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125511, d124189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d122306 q = 1) (hb : d125517 q = 1) : d124223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125517, d124223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125517, d124223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36227 q ha hb
  have h18 (q : Pattern) (ha : d14454 q = 1) (hb : d122306 q = 1) : d124234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14454, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14454, d124234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36205 q ha hb
  have h19 (q : Pattern) (ha : d122306 q = 1) (hb : d125518 q = 1) : d124235 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125518, d124235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125518, d124235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d122306 q = 1) (hb : d125519 q = 1) : d124236 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125519, d124236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125519, d124236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d122306 q = 1) (hb : d125520 q = 1) : d124237 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125520, d124237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125520, d124237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d122306 q = 1) (hb : d125521 q = 1) : d124238 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125521, d124238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125521, d124238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d122306 q = 1) (hb : d125522 q = 1) : d124239 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125522, d124239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125522, d124239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro36229 (p : Pattern) (ha : d122306 p = 1) (hb : d125528 p = 1) : d124245 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d122306 q = 1) (hb : d125523 q = 1) : d124240 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125523, d124240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125523, d124240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36228 q ha hb
  have h2 (q : Pattern) (ha : d122306 q = 1) (hb : d125524 q = 1) : d124241 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125524, d124241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125524, d124241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d122306 q = 1) (hb : d125525 q = 1) : d124242 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125525, d124242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125525, d124242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d122306 q = 1) (hb : d125526 q = 1) : d124243 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125526, d124243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125526, d124243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d122306 q = 1) (hb : d125527 q = 1) : d124244 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125527, d124244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125527, d124244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d122306 q = 1) (hb : d125528 q = 1) : d124245 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125528, d124245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d125528, d124245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36230 (p : Pattern) (ha : d14477 p = 1) (hb : d122306 p = 1) : d124252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14468 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
    | true =>
      simp only [d14468, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
  have h2 (q : Pattern) (ha : d14469 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14469, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14470 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14473 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14474 q = 1) (hb : d122306 q = 1) : d124121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14474, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14471 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
    | true =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14472 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14473 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14475 q = 1) (hb : d122306 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14475, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14476 q = 1) (hb : d122306 q = 1) : d124251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14476, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14476, d124251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d14477 q = 1) (hb : d122306 q = 1) : d124252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14477, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14477, d124252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro36231 (p : Pattern) (ha : d14481 p = 1) (hb : d122306 p = 1) : d124256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d122305 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14471 q = 1) (hb : d122305 q = 1) : d124247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
    | true =>
      simp only [d14471, d124247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14472 q = 1) (hb : d122305 q = 1) : d124248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, d124248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14473 q = 1) (hb : d122305 q = 1) : d124249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d124249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14475 q = 1) (hb : d122306 q = 1) : d124250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14475, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14475, d122306, d124250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14480 q = 1) (hb : d122306 q = 1) : d124255 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14480, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14480, d124255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14481 q = 1) (hb : d122306 q = 1) : d124256 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14481, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14481, d124256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro36232 (p : Pattern) (ha : d14487 p = 1) (hb : d122306 p = 1) : d124262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d122306 q = 1) : d124261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14487 q = 1) (hb : d122306 q = 1) : d124262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14487, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14487, d124262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36233 (p : Pattern) (ha : d14491 p = 1) (hb : d122306 p = 1) : d124266 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d122306 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d122306 q = 1) : d124265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14491 q = 1) (hb : d122306 q = 1) : d124266 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14491, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14491, d124266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36234 (p : Pattern) (ha : d14497 p = 1) (hb : d122306 p = 1) : d124272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d122306 q = 1) : d124267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36232 q ha hb
    | true =>
      simp only [d14492, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36233 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d122306 q = 1) : d124268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d122306 q = 1) : d124269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d122306 q = 1) : d124270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d122306 q = 1) : d124271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14497 q = 1) (hb : d122306 q = 1) : d124272 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, d124272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36235 (p : Pattern) (ha : d14500 p = 1) (hb : d122306 p = 1) : d124275 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d122306 q = 1) : d124261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, d124261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14500 q = 1) (hb : d122306 q = 1) : d124275 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14500, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14500, d124275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro36236 (p : Pattern) (ha : d14501 p = 1) (hb : d122306 p = 1) : d124276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d122306 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d122306 q = 1) : d124265 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, d124265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14501 q = 1) (hb : d122306 q = 1) : d124276 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14501, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14501, d124276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36237 (p : Pattern) (ha : d14507 p = 1) (hb : d122306 p = 1) : d124282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d122306 q = 1) : d124267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36232 q ha hb
    | true =>
      simp only [d14492, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36233 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d122306 q = 1) : d124268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d122306 q = 1) : d124269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d122306 q = 1) : d124270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d122306 q = 1) : d124271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14502 q = 1) (hb : d122306 q = 1) : d124277 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36235 q ha hb
    | true =>
      simp only [d14502, d124277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36236 q ha hb
  have h7 (q : Pattern) (ha : d14503 q = 1) (hb : d122306 q = 1) : d124278 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, d124278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14504 q = 1) (hb : d122306 q = 1) : d124279 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14504, d124279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14505 q = 1) (hb : d122306 q = 1) : d124280 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d124280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14506 q = 1) (hb : d122306 q = 1) : d124281 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d124281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14507 q = 1) (hb : d122306 q = 1) : d124282 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14507, d124282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36238 (p : Pattern) (ha : d14622 p = 1) (hb : d122306 p = 1) : d124355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d122306 q = 1) : d124267 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36232 q ha hb
    | true =>
      simp only [d14492, d124267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36233 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d122306 q = 1) : d124268 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d124268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d122306 q = 1) : d124269 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d124269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d122306 q = 1) : d124270 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d124270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d122306 q = 1) : d124271 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d124271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14617 q = 1) (hb : d122306 q = 1) : d124350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36233 q ha hb
    | true =>
      simp only [d14617, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14618 q = 1) (hb : d122306 q = 1) : d124351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14619 q = 1) (hb : d122306 q = 1) : d124352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14619, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14620 q = 1) (hb : d122306 q = 1) : d124353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14621 q = 1) (hb : d122306 q = 1) : d124354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14622 q = 1) (hb : d122306 q = 1) : d124355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14622, d124355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14622, d124355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36239 (p : Pattern) (ha : d14628 p = 1) (hb : d122306 p = 1) : d124361 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14617 q = 1) (hb : d122306 q = 1) : d124350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36233 q ha hb
    | true =>
      simp only [d14617, d124350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14618 q = 1) (hb : d122306 q = 1) : d124351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, d124351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14619 q = 1) (hb : d122306 q = 1) : d124352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14619, d124352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14620 q = 1) (hb : d122306 q = 1) : d124353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, d124353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14621 q = 1) (hb : d122306 q = 1) : d124354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, d124354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14623 q = 1) (hb : d122306 q = 1) : d124356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36236 q ha hb
    | true =>
      simp only [d14623, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14624 q = 1) (hb : d122306 q = 1) : d124357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14625 q = 1) (hb : d122306 q = 1) : d124358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14625, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14626 q = 1) (hb : d122306 q = 1) : d124359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14627 q = 1) (hb : d122306 q = 1) : d124360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14628 q = 1) (hb : d122306 q = 1) : d124361 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14628, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14628, d124361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro36240 (p : Pattern) (ha : d14637 p = 1) (hb : d122306 p = 1) : d124370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14623 q = 1) (hb : d122306 q = 1) : d124356 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36236 q ha hb
    | true =>
      simp only [d14623, d124356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14624 q = 1) (hb : d122306 q = 1) : d124357 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, d124357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14625 q = 1) (hb : d122306 q = 1) : d124358 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14625, d124358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14626 q = 1) (hb : d122306 q = 1) : d124359 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, d124359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14627 q = 1) (hb : d122306 q = 1) : d124360 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, d124360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14637 q = 1) (hb : d122306 q = 1) : d124370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14637, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14637, d124370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36241 (p : Pattern) (ha : d14680 p = 1) (hb : d122306 p = 1) : d124398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d122305 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14662 q = 1) (hb : d122305 q = 1) : d124385 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34559 q ha hb
    | true =>
      simp only [d14662, d124385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14663 q = 1) (hb : d122305 q = 1) : d124386 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, d124386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14664 q = 1) (hb : d122305 q = 1) : d124387 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d124387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14670 q = 1) (hb : d122306 q = 1) : d124388 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14670, d122306, d124388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d14679 q = 1) (hb : d122306 q = 1) : d124397 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14679, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14679, d124397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14680 q = 1) (hb : d122306 q = 1) : d124398 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14680, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14680, d124398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h9 p ha hb
theorem andIntro36242 (p : Pattern) (ha : d14736 p = 1) (hb : d122306 p = 1) : d124421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14681 q = 1) (hb : d122306 q = 1) : d124399 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36241 q ha hb
    | true =>
      simp only [d14681, d124399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14682 q = 1) (hb : d122306 q = 1) : d124400 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, d124400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14733 q = 1) (hb : d122306 q = 1) : d124418 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14733, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14733, d124418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14734 q = 1) (hb : d122306 q = 1) : d124419 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14734, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14734, d124419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14735 q = 1) (hb : d122306 q = 1) : d124420 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14735, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14735, d124420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14736 q = 1) (hb : d122306 q = 1) : d124421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14736, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14736, d124421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro36243 (p : Pattern) (ha : d14742 p = 1) (hb : d122306 p = 1) : d124427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14737 q = 1) (hb : d122306 q = 1) : d124422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14737, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36242 q ha hb
    | true =>
      simp only [d14737, d124422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14738 q = 1) (hb : d122306 q = 1) : d124423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14738, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14738, d124423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14739 q = 1) (hb : d122306 q = 1) : d124424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14739, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14739, d124424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14740 q = 1) (hb : d122306 q = 1) : d124425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14740, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14740, d124425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14741 q = 1) (hb : d122306 q = 1) : d124426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14741, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14741, d124426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14742 q = 1) (hb : d122306 q = 1) : d124427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14742, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14742, d124427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36244 (p : Pattern) (ha : d14512 p = 1) (hb : d122306 p = 1) : d124287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d122306 q = 1) : d124260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d124260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d122306 q = 1) : d124286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, d124286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14512 q = 1) (hb : d122306 q = 1) : d124287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14512, d124287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14512, d124287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36245 (p : Pattern) (ha : d14514 p = 1) (hb : d122306 p = 1) : d124289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d122306 q = 1) : d124264 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d124264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d122306 q = 1) : d124288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, d124288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14514 q = 1) (hb : d122306 q = 1) : d124289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14514, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14514, d124289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36246 (p : Pattern) (ha : d14521 p = 1) (hb : d122306 p = 1) : d124296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d122306 q = 1) : d124259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d124259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d122306 q = 1) : d124294 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, d124294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d122306 q = 1) : d124295 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, d124295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14521 q = 1) (hb : d122306 q = 1) : d124296 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14521, d124296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14521, d124296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro36247 (p : Pattern) (ha : d14524 p = 1) (hb : d122306 p = 1) : d124299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d122306 q = 1) : d124257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36231 q ha hb
    | true =>
      simp only [d14482, d124257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d122306 q = 1) : d124258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d124258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d122306 q = 1) : d124263 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d124263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d122306 q = 1) : d124297 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, d124297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d122306 q = 1) : d124298 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, d124298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14524 q = 1) (hb : d122306 q = 1) : d124299 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14524, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14524, d124299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro36248 (p : Pattern) (ha : d14542 p = 1) (hb : d122306 p = 1) : d124309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14533 q = 1) (hb : d122305 q = 1) : d124304 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14533, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34567 q ha hb
    | true =>
      simp only [d14533, d124304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
  have h2 (q : Pattern) (ha : d14534 q = 1) (hb : d122305 q = 1) : d124305 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14534, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14534, d124305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14535 q = 1) (hb : d122305 q = 1) : d124306 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14535, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14535, d124306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14539 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d14540 q = 1) (hb : d122306 q = 1) : d124307 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14540, d122306, d124307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14540, d122306, d124307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d14468 q = 1) (hb : d122305 q = 1) : d124118 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34523 q ha hb
    | true =>
      simp only [d14468, d124118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34547 q ha hb
  have h7 (q : Pattern) (ha : d14469 q = 1) (hb : d122305 q = 1) : d124119 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14469, d124119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14470 q = 1) (hb : d122305 q = 1) : d124120 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, d124120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d14473 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d14474 q = 1) (hb : d122306 q = 1) : d124121 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14474, d122306, d124121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d14541 q = 1) (hb : d122306 q = 1) : d124308 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14541, d124308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14541, d124308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d14542 q = 1) (hb : d122306 q = 1) : d124309 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14542, d124309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14542, d124309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro36249 (p : Pattern) (ha : d14548 p = 1) (hb : d122306 p = 1) : d124315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d122306 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d122306 q = 1) : d124310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36248 q ha hb
    | true =>
      simp only [d14543, d124310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d122306 q = 1) : d124311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, d124311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d122306 q = 1) : d124253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36230 q ha hb
    | true =>
      simp only [d14478, d124253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d122306 q = 1) : d124254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d124254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d122306 q = 1) : d124312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, d124312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d122306 q = 1) : d124313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, d124313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d122306 q = 1) : d124314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, d124314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14548 q = 1) (hb : d122306 q = 1) : d124315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14548, d124315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14548, d124315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
