import NetHack.Soko22Hazard87.AndIntroBlocks0055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro14000 (p : Pattern) (ha : d6799 p = 1) (hb : d92315 p = 1) : d98845 p = 1 := by
  have h0 (q : Pattern) (ha : d6797 q = 1) (hb : d92313 q = 1) : d6797 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4822 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6798 q = 1) (hb : d92315 q = 1) : d98844 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6798, d92315, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6798, d92315, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6799 q = 1) (hb : d92315 q = 1) : d98845 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6799, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6799, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14001 (p : Pattern) (ha : d6805 p = 1) (hb : d98800 p = 1) : d98851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d555 q = 1) (hb : d77842 q = 1) : d7466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9835 q ha hb
    | true =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d556 q = 1) (hb : d77842 q = 1) : d7467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6800 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14000 q ha hb
    | true =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6801 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6802 q = 1) (hb : d98800 q = 1) : d98848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6802, d98800, d98848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6802, d98800, d98848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6803 q = 1) (hb : d98800 q = 1) : d98849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6803, d98849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6803, d98849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6804 q = 1) (hb : d98800 q = 1) : d98850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6804, d98850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6804, d98850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6805 q = 1) (hb : d98800 q = 1) : d98851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6805, d98851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6805, d98851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14002 (p : Pattern) (ha : d82071 p = 1) (hb : d98800 p = 1) : d98857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d98800 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d515 q = 1) (hb : d98800 q = 1) : d7454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d7454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13997 q ha hb
    | true =>
      simp only [d515, d7454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d98800 q = 1) : d7455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d7455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d7455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d98800 q = 1) : d7456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d7456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, d7456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d98800 q = 1) : d7457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d7457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d7457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d98800 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d525 q = 1) (hb : d98800 q = 1) : d7461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d7461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13998 q ha hb
    | true =>
      simp only [d525, d7461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d526 q = 1) (hb : d98800 q = 1) : d7462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d7462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d7462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d527 q = 1) (hb : d98800 q = 1) : d7463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d7463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d527, d7463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6810 q = 1) (hb : d98800 q = 1) : d98852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6810, d98852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14001 q ha hb
    | true =>
      simp only [d6810, d98852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13995 q ha hb
  have h11 (q : Pattern) (ha : d82067 q = 1) (hb : d98800 q = 1) : d98853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82067, d98853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82067, d98853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5400 q = 1) (hb : d98800 q = 1) : d7487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13999 q ha hb
    | true =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5401 q = 1) (hb : d98800 q = 1) : d7488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82068 q = 1) (hb : d98800 q = 1) : d98854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82068, d98854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82068, d98854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82069 q = 1) (hb : d98800 q = 1) : d98855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82069, d98855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82069, d98855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82070 q = 1) (hb : d98800 q = 1) : d98856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82070, d98856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82070, d98856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82071 q = 1) (hb : d98800 q = 1) : d98857 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82071, d98857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82071, d98857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro14003 (p : Pattern) (ha : d609 p = 1) (hb : d98800 p = 1) : d7493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d98800 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d98800, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d484, d98800, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d485 q = 1) (hb : d98800 q = 1) : d7431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d485, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d511 q = 1) (hb : d98800 q = 1) : d7452 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d7452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d7452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d609 q = 1) (hb : d98800 q = 1) : d7493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d609, d7493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d609, d7493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14004 (p : Pattern) (ha : d615 p = 1) (hb : d98800 p = 1) : d7498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d484 q = 1) (hb : d98800 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d98800, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d484, d98800, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d519 q = 1) (hb : d98800 q = 1) : d7458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d7458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d7458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d520 q = 1) (hb : d98800 q = 1) : d7459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d7459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d520, d7459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d615 q = 1) (hb : d98800 q = 1) : d7498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d615, d7498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d615, d7498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14005 (p : Pattern) (ha : d5406 p = 1) (hb : d98800 p = 1) : d7507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d478 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8191 q ha hb
    | true =>
      simp only [d478, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d479 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d479, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5396 q = 1) (hb : d98800 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5396, d98800, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5396, d98800, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5397 q = 1) (hb : d98800 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5397, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5398 q = 1) (hb : d98800 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5398, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5406 q = 1) (hb : d98800 q = 1) : d7507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5406, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5406, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14006 (p : Pattern) (ha : d6816 p = 1) (hb : d98800 p = 1) : d98858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d555 q = 1) (hb : d77842 q = 1) : d7466 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9835 q ha hb
    | true =>
      simp only [d555, d7466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d556 q = 1) (hb : d77842 q = 1) : d7467 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d556, d7467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6800 q = 1) (hb : d92315 q = 1) : d98846 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14000 q ha hb
    | true =>
      simp only [d6800, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6801 q = 1) (hb : d92315 q = 1) : d98847 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6801, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6802 q = 1) (hb : d98800 q = 1) : d98848 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6802, d98800, d98848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6802, d98800, d98848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6803 q = 1) (hb : d98800 q = 1) : d98849 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6803, d98849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6803, d98849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6804 q = 1) (hb : d98800 q = 1) : d98850 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6804, d98850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6804, d98850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d6816 q = 1) (hb : d98800 q = 1) : d98858 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6816, d98858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6816, d98858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14007 (p : Pattern) (ha : d6817 p = 1) (hb : d98800 p = 1) : d7442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4825 q = 1) (hb : d77842 q = 1) : d7327 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4825, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9830 q ha hb
    | true =>
      simp only [d4825, d7327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4826 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4826, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4826, d7328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d92315 q = 1) : d483 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6806 q = 1) (hb : d98800 q = 1) : d7430 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6806, d98800, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6806, d98800, d7430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6807 q = 1) (hb : d98800 q = 1) : d7431 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6807, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6807, d7431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6808 q = 1) (hb : d98800 q = 1) : d7432 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6808, d7432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6808, d7432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6817 q = 1) (hb : d98800 q = 1) : d7442 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6817, d7442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6817, d7442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14008 (p : Pattern) (ha : d82076 p = 1) (hb : d98800 p = 1) : d98864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d98800 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d515 q = 1) (hb : d98800 q = 1) : d7454 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d7454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13997 q ha hb
    | true =>
      simp only [d515, d7454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d98800 q = 1) : d7455 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d7455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d7455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d98800 q = 1) : d7456 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d7456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, d7456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d98800 q = 1) : d7457 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d7457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d7457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d98800 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d525 q = 1) (hb : d98800 q = 1) : d7461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d7461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13998 q ha hb
    | true =>
      simp only [d525, d7461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d526 q = 1) (hb : d98800 q = 1) : d7462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d7462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d7462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d527 q = 1) (hb : d98800 q = 1) : d7463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d7463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d527, d7463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6810 q = 1) (hb : d98800 q = 1) : d98852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6810, d98852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14001 q ha hb
    | true =>
      simp only [d6810, d98852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13995 q ha hb
  have h11 (q : Pattern) (ha : d82067 q = 1) (hb : d98800 q = 1) : d98853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82067, d98853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82067, d98853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d5400 q = 1) (hb : d98800 q = 1) : d7487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13999 q ha hb
    | true =>
      simp only [d5400, d7487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5401 q = 1) (hb : d98800 q = 1) : d7488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5401, d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82068 q = 1) (hb : d98800 q = 1) : d98854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82068, d98854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82068, d98854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82069 q = 1) (hb : d98800 q = 1) : d98855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82069, d98855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82069, d98855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82070 q = 1) (hb : d98800 q = 1) : d98856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82070, d98856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82070, d98856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d610 q = 1) (hb : d98800 q = 1) : d610 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d611 q = 1) (hb : d98800 q = 1) : d7494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d7494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14003 q ha hb
    | true =>
      simp only [d611, d7494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d612 q = 1) (hb : d98800 q = 1) : d7495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d7495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d612, d7495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d613 q = 1) (hb : d98800 q = 1) : d7496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d7496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d613, d7496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d614 q = 1) (hb : d98800 q = 1) : d7497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d7497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d7497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d616 q = 1) (hb : d98800 q = 1) : d616 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d617 q = 1) (hb : d98800 q = 1) : d7499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d7499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14004 q ha hb
    | true =>
      simp only [d617, d7499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d618 q = 1) (hb : d98800 q = 1) : d7500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d7500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d618, d7500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d619 q = 1) (hb : d98800 q = 1) : d7501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d7501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d619, d7501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6818 q = 1) (hb : d98800 q = 1) : d98859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6818, d98859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14006 q ha hb
    | true =>
      simp only [d6818, d98859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14007 q ha hb
  have h27 (q : Pattern) (ha : d82072 q = 1) (hb : d98800 q = 1) : d98860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82072, d98860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82072, d98860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5407 q = 1) (hb : d98800 q = 1) : d7508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14005 q ha hb
    | true =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5408 q = 1) (hb : d98800 q = 1) : d7509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d82073 q = 1) (hb : d98800 q = 1) : d98861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82073, d98861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d82073, d98861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d82074 q = 1) (hb : d98800 q = 1) : d98862 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82074, d98862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d82074, d98862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d82075 q = 1) (hb : d98800 q = 1) : d98863 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82075, d98863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82075, d98863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d82076 q = 1) (hb : d98800 q = 1) : d98864 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82076, d98864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82076, d98864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro14009 (p : Pattern) (ha : d82083 p = 1) (hb : d98800 p = 1) : d98871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6818 q = 1) (hb : d98800 q = 1) : d98859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6818, d98859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14006 q ha hb
    | true =>
      simp only [d6818, d98859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14007 q ha hb
  have h2 (q : Pattern) (ha : d82072 q = 1) (hb : d98800 q = 1) : d98860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82072, d98860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82072, d98860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5407 q = 1) (hb : d98800 q = 1) : d7508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14005 q ha hb
    | true =>
      simp only [d5407, d7508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5408 q = 1) (hb : d98800 q = 1) : d7509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5408, d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82073 q = 1) (hb : d98800 q = 1) : d98861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82073, d98861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82073, d98861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82081 q = 1) (hb : d98800 q = 1) : d98869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82081, d98869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82081, d98869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82082 q = 1) (hb : d98800 q = 1) : d98870 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82082, d98870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82082, d98870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82083 q = 1) (hb : d98800 q = 1) : d98871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82083, d98871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82083, d98871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14010 (p : Pattern) (ha : d5428 p = 1) (hb : d98800 p = 1) : d7554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8199 q ha hb
    | true =>
      simp only [d676, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5425 q = 1) (hb : d98800 q = 1) : d7551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5425, d98800, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5425, d98800, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5426 q = 1) (hb : d98800 q = 1) : d7552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5426, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5426, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d5427 q = 1) (hb : d98800 q = 1) : d7553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5427, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5427, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d5428 q = 1) (hb : d98800 q = 1) : d7554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5428, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5428, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14011 (p : Pattern) (ha : d6845 p = 1) (hb : d92315 p = 1) : d98878 p = 1 := by
  have h0 (q : Pattern) (ha : d6843 q = 1) (hb : d92313 q = 1) : d6843 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6082 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6844 q = 1) (hb : d92315 q = 1) : d98877 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6844, d92315, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6844, d92315, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6845 q = 1) (hb : d92315 q = 1) : d98878 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6845, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6845, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14012 (p : Pattern) (ha : d6851 p = 1) (hb : d98800 p = 1) : d98884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d671 q = 1) (hb : d77842 q = 1) : d7530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d671, d7530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9845 q ha hb
    | true =>
      simp only [d671, d7530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d672 q = 1) (hb : d77842 q = 1) : d7531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d672, d7531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d672, d7531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6846 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14011 q ha hb
    | true =>
      simp only [d6846, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6847 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6847, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6848 q = 1) (hb : d98800 q = 1) : d98881 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6848, d98800, d98881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6848, d98800, d98881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6849 q = 1) (hb : d98800 q = 1) : d98882 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6849, d98882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6849, d98882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6850 q = 1) (hb : d98800 q = 1) : d98883 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6850, d98883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6850, d98883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d6851 q = 1) (hb : d98800 q = 1) : d98884 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6851, d98884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6851, d98884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14013 (p : Pattern) (ha : d6855 p = 1) (hb : d98800 p = 1) : d7539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6085 q = 1) (hb : d77842 q = 1) : d7391 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6085, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9847 q ha hb
    | true =>
      simp only [d6085, d7391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6086 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6086, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6086, d7392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d685 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6852 q = 1) (hb : d98800 q = 1) : d7536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6852, d98800, d7536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6852, d98800, d7536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6853 q = 1) (hb : d98800 q = 1) : d7537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6853, d7537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6853, d7537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6854 q = 1) (hb : d98800 q = 1) : d7538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6854, d7538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6854, d7538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6855 q = 1) (hb : d98800 q = 1) : d7539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6855, d7539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6855, d7539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14014 (p : Pattern) (ha : d82093 p = 1) (hb : d98800 p = 1) : d98890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6856 q = 1) (hb : d98800 q = 1) : d98885 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6856, d98885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14012 q ha hb
    | true =>
      simp only [d6856, d98885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14013 q ha hb
  have h2 (q : Pattern) (ha : d82089 q = 1) (hb : d98800 q = 1) : d98886 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82089, d98886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82089, d98886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5429 q = 1) (hb : d98800 q = 1) : d7555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5429, d7555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14010 q ha hb
    | true =>
      simp only [d5429, d7555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5430 q = 1) (hb : d98800 q = 1) : d7556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5430, d7556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5430, d7556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82090 q = 1) (hb : d98800 q = 1) : d98887 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82090, d98887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82090, d98887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82091 q = 1) (hb : d98800 q = 1) : d98888 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82091, d98888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82091, d98888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82092 q = 1) (hb : d98800 q = 1) : d98889 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82092, d98889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82092, d98889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82093 q = 1) (hb : d98800 q = 1) : d98890 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82093, d98890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82093, d98890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14015 (p : Pattern) (ha : d82099 p = 1) (hb : d98800 p = 1) : d98896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d98800 q = 1) : d7440 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d7440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d7440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13992 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d98800 q = 1) : d7441 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d7441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d7441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d98800 q = 1) : d7449 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d7449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13992 q ha hb
    | true =>
      simp only [d508, d7449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13994 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d98800 q = 1) : d7450 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d7450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d7450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d98800 q = 1) : d7451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d7451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d7451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82077 q = 1) (hb : d98800 q = 1) : d98865 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82077, d98865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14002 q ha hb
    | true =>
      simp only [d82077, d98865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14008 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d98800 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6831 q = 1) (hb : d98800 q = 1) : d7516 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6831, d7516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13996 q ha hb
    | true =>
      simp only [d6831, d7516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82078 q = 1) (hb : d98800 q = 1) : d98866 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82078, d98866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82078, d98866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82079 q = 1) (hb : d98800 q = 1) : d98867 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82079, d98867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82079, d98867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d82080 q = 1) (hb : d98800 q = 1) : d98868 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82080, d98868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82080, d98868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d82084 q = 1) (hb : d98800 q = 1) : d98872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82084, d98872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82084, d98872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14009 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d98800 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d82085 q = 1) (hb : d98800 q = 1) : d98873 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82085, d98873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82085, d98873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82086 q = 1) (hb : d98800 q = 1) : d98874 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82086, d98874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82086, d98874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82087 q = 1) (hb : d98800 q = 1) : d98875 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82087, d98875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82087, d98875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d82088 q = 1) (hb : d98800 q = 1) : d98876 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82088, d98876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82088, d98876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d82094 q = 1) (hb : d98800 q = 1) : d98891 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82094, d98891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82094, d98891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14014 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d98800 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d82095 q = 1) (hb : d98800 q = 1) : d98892 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82095, d98892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82095, d98892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d82096 q = 1) (hb : d98800 q = 1) : d98893 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82096, d98893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82096, d98893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82097 q = 1) (hb : d98800 q = 1) : d98894 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82097, d98894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82097, d98894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82098 q = 1) (hb : d98800 q = 1) : d98895 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82098, d98895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82098, d98895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d82099 q = 1) (hb : d98800 q = 1) : d98896 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82099, d98896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82099, d98896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro14016 (p : Pattern) (ha : d82105 p = 1) (hb : d98800 p = 1) : d98902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82100 q = 1) (hb : d98800 q = 1) : d98897 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82100, d98897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82100, d98897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14015 q ha hb
  have h2 (q : Pattern) (ha : d82101 q = 1) (hb : d98800 q = 1) : d98898 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82101, d98898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82101, d98898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82102 q = 1) (hb : d98800 q = 1) : d98899 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82102, d98899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82102, d98899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82103 q = 1) (hb : d98800 q = 1) : d98900 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82103, d98900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82103, d98900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82104 q = 1) (hb : d98800 q = 1) : d98901 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82104, d98901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82104, d98901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82105 q = 1) (hb : d98800 q = 1) : d98902 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82105, d98902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82105, d98902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14017 (p : Pattern) (ha : d779 p = 1) (hb : d98800 p = 1) : d7581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d98800 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d98800 q = 1) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d778 q = 1) (hb : d98800 q = 1) : d7580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d778, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d779 q = 1) (hb : d98800 q = 1) : d7581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d779, d7581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d779, d7581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14018 (p : Pattern) (ha : d789 p = 1) (hb : d98800 p = 1) : d7587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d98800 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d784 q = 1) (hb : d98800 q = 1) : d7582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14017 q ha hb
    | true =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d98800 q = 1) : d7583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d98800 q = 1) : d7584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d98800 q = 1) : d7585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d98800 q = 1) : d7586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d789 q = 1) (hb : d98800 q = 1) : d7587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d7587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d7587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14019 (p : Pattern) (ha : d792 p = 1) (hb : d98800 p = 1) : d7590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d776 q = 1) (hb : d98800 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d98800 q = 1) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d778 q = 1) (hb : d98800 q = 1) : d7580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d778, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d792 q = 1) (hb : d98800 q = 1) : d7590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d792, d7590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d792, d7590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14020 (p : Pattern) (ha : d799 p = 1) (hb : d98800 p = 1) : d7596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d98800 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d784 q = 1) (hb : d98800 q = 1) : d7582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14017 q ha hb
    | true =>
      simp only [d784, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d98800 q = 1) : d7583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d786 q = 1) (hb : d98800 q = 1) : d7584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d787 q = 1) (hb : d98800 q = 1) : d7585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d788 q = 1) (hb : d98800 q = 1) : d7586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d98800 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d794 q = 1) (hb : d98800 q = 1) : d7591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d7591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14019 q ha hb
    | true =>
      simp only [d794, d7591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d795 q = 1) (hb : d98800 q = 1) : d7592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d7592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d7592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d796 q = 1) (hb : d98800 q = 1) : d7593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d7593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d796, d7593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d797 q = 1) (hb : d98800 q = 1) : d7594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d7594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d7594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d798 q = 1) (hb : d98800 q = 1) : d7595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d7595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d7595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d799 q = 1) (hb : d98800 q = 1) : d7596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d7596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d799, d7596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro14021 (p : Pattern) (ha : d6887 p = 1) (hb : d98800 p = 1) : d7581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4920 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9856 q ha hb
    | true =>
      simp only [d4920, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4921 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4921, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6884 q = 1) (hb : d98800 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6884, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6884, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6885 q = 1) (hb : d98800 q = 1) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6885, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6885, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6886 q = 1) (hb : d98800 q = 1) : d7580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6886, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6886, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6887 q = 1) (hb : d98800 q = 1) : d7581 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6887, d7581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6887, d7581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14022 (p : Pattern) (ha : d6908 p = 1) (hb : d98800 p = 1) : d7663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d98800 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6903 q = 1) (hb : d98800 q = 1) : d7582 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6903, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14021 q ha hb
    | true =>
      simp only [d6903, d7582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6904 q = 1) (hb : d98800 q = 1) : d7583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6904, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6904, d7583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6905 q = 1) (hb : d98800 q = 1) : d7584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6905, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6905, d7584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6906 q = 1) (hb : d98800 q = 1) : d7585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6906, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6906, d7585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6907 q = 1) (hb : d98800 q = 1) : d7586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6907, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6907, d7586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d98800 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6908 q = 1) (hb : d98800 q = 1) : d7663 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6908, d7663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6908, d7663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14023 (p : Pattern) (ha : d804 p = 1) (hb : d98800 p = 1) : d7601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d98800 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d98800 q = 1) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d98800 q = 1) : d7600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d7600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d7600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d804 q = 1) (hb : d98800 q = 1) : d7601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d804, d7601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d804, d7601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14024 (p : Pattern) (ha : d813 p = 1) (hb : d98800 p = 1) : d7608 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d98800 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d98800 q = 1) : d7606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d7606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d7606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d98800 q = 1) : d7607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d7607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d7607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d813 q = 1) (hb : d98800 q = 1) : d7608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, d7608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, d7608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14025 (p : Pattern) (ha : d6118 p = 1) (hb : d98800 p = 1) : d7634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6115 q = 1) (hb : d98800 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d98800, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6115, d98800, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d98800 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6117 q = 1) (hb : d98800 q = 1) : d7633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6117, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6118 q = 1) (hb : d98800 q = 1) : d7634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6118, d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6118, d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14026 (p : Pattern) (ha : d6877 p = 1) (hb : d92315 p = 1) : d98905 p = 1 := by
  have h0 (q : Pattern) (ha : d6875 q = 1) (hb : d92313 q = 1) : d6875 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6876 q = 1) (hb : d92315 q = 1) : d98904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6876, d92315, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6876, d92315, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6877 q = 1) (hb : d92315 q = 1) : d98905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6877, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6877, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14027 (p : Pattern) (ha : d6883 p = 1) (hb : d98800 p = 1) : d98911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d846 q = 1) (hb : d77842 q = 1) : d7614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d7614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9861 q ha hb
    | true =>
      simp only [d846, d7614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d847 q = 1) (hb : d77842 q = 1) : d7615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d7615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d847, d7615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6878 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14026 q ha hb
    | true =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6879 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6880 q = 1) (hb : d98800 q = 1) : d98908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6880, d98800, d98908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6880, d98800, d98908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6881 q = 1) (hb : d98800 q = 1) : d98909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6881, d98909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6881, d98909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6882 q = 1) (hb : d98800 q = 1) : d98910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6882, d98910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6882, d98910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6883 q = 1) (hb : d98800 q = 1) : d98911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6883, d98911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6883, d98911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14028 (p : Pattern) (ha : d82111 p = 1) (hb : d98800 p = 1) : d98917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d98800 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d807 q = 1) (hb : d98800 q = 1) : d7602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d7602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14023 q ha hb
    | true =>
      simp only [d807, d7602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d98800 q = 1) : d7603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d7603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d7603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d809 q = 1) (hb : d98800 q = 1) : d7604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d7604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, d7604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d810 q = 1) (hb : d98800 q = 1) : d7605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d7605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d7605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d98800 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d817 q = 1) (hb : d98800 q = 1) : d7609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d7609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14024 q ha hb
    | true =>
      simp only [d817, d7609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d818 q = 1) (hb : d98800 q = 1) : d7610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d7610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d7610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d819 q = 1) (hb : d98800 q = 1) : d7611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d7611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d819, d7611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6888 q = 1) (hb : d98800 q = 1) : d98912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6888, d98912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14027 q ha hb
    | true =>
      simp only [d6888, d98912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14021 q ha hb
  have h11 (q : Pattern) (ha : d82107 q = 1) (hb : d98800 q = 1) : d98913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82107, d98913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82107, d98913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6160 q = 1) (hb : d98800 q = 1) : d7635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d7635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14025 q ha hb
    | true =>
      simp only [d6160, d7635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6161 q = 1) (hb : d98800 q = 1) : d7636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6161, d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82108 q = 1) (hb : d98800 q = 1) : d98914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82108, d98914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82108, d98914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82109 q = 1) (hb : d98800 q = 1) : d98915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82109, d98915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82109, d98915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82110 q = 1) (hb : d98800 q = 1) : d98916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82110, d98916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82110, d98916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82111 q = 1) (hb : d98800 q = 1) : d98917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82111, d98917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82111, d98917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro14029 (p : Pattern) (ha : d915 p = 1) (hb : d98800 p = 1) : d7641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d98800 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d98800 q = 1) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d98800 q = 1) : d7600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d7600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d7600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d915 q = 1) (hb : d98800 q = 1) : d7641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d915, d7641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d915, d7641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14030 (p : Pattern) (ha : d921 p = 1) (hb : d98800 p = 1) : d7646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d98800 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d776, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d98800 q = 1) : d7606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d7606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d7606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d98800 q = 1) : d7607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d7607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d7607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d921 q = 1) (hb : d98800 q = 1) : d7646 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, d7646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d921, d7646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14031 (p : Pattern) (ha : d6127 p = 1) (hb : d98800 p = 1) : d7655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8219 q ha hb
    | true =>
      simp only [d770, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6115 q = 1) (hb : d98800 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6115, d98800, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6115, d98800, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6116 q = 1) (hb : d98800 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6116, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6117 q = 1) (hb : d98800 q = 1) : d7633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6117, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6117, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6127 q = 1) (hb : d98800 q = 1) : d7655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6127, d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6127, d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14032 (p : Pattern) (ha : d6894 p = 1) (hb : d98800 p = 1) : d98918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d77842 q = 1) : d7614 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d7614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9861 q ha hb
    | true =>
      simp only [d846, d7614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d77842 q = 1) : d7615 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d7615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d7615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6878 q = 1) (hb : d92315 q = 1) : d98906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14026 q ha hb
    | true =>
      simp only [d6878, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6879 q = 1) (hb : d92315 q = 1) : d98907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6879, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6880 q = 1) (hb : d98800 q = 1) : d98908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6880, d98800, d98908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6880, d98800, d98908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6881 q = 1) (hb : d98800 q = 1) : d98909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6881, d98909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6881, d98909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6882 q = 1) (hb : d98800 q = 1) : d98910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6882, d98910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6882, d98910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d6894 q = 1) (hb : d98800 q = 1) : d98918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6894, d98918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6894, d98918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14033 (p : Pattern) (ha : d6895 p = 1) (hb : d98800 p = 1) : d7590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4920 q = 1) (hb : d77842 q = 1) : d7576 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d4920, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9856 q ha hb
    | true =>
      simp only [d4920, d7576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4921 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d4921, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4921, d7577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d92315 q = 1) : d775 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6884 q = 1) (hb : d98800 q = 1) : d7578 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6884, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6884, d98800, d7578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6885 q = 1) (hb : d98800 q = 1) : d7579 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6885, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6885, d7579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6886 q = 1) (hb : d98800 q = 1) : d7580 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6886, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6886, d7580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6895 q = 1) (hb : d98800 q = 1) : d7590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6895, d7590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6895, d7590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14034 (p : Pattern) (ha : d82116 p = 1) (hb : d98800 p = 1) : d98924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d98800 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d807 q = 1) (hb : d98800 q = 1) : d7602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d7602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14023 q ha hb
    | true =>
      simp only [d807, d7602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d98800 q = 1) : d7603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d7603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d7603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d809 q = 1) (hb : d98800 q = 1) : d7604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d7604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, d7604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d810 q = 1) (hb : d98800 q = 1) : d7605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d7605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d7605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d98800 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d817 q = 1) (hb : d98800 q = 1) : d7609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d7609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14024 q ha hb
    | true =>
      simp only [d817, d7609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d818 q = 1) (hb : d98800 q = 1) : d7610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d7610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d7610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d819 q = 1) (hb : d98800 q = 1) : d7611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d7611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d819, d7611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6888 q = 1) (hb : d98800 q = 1) : d98912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6888, d98912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14027 q ha hb
    | true =>
      simp only [d6888, d98912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14021 q ha hb
  have h11 (q : Pattern) (ha : d82107 q = 1) (hb : d98800 q = 1) : d98913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82107, d98913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82107, d98913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6160 q = 1) (hb : d98800 q = 1) : d7635 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6160, d7635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14025 q ha hb
    | true =>
      simp only [d6160, d7635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6161 q = 1) (hb : d98800 q = 1) : d7636 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6161, d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6161, d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82108 q = 1) (hb : d98800 q = 1) : d98914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82108, d98914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82108, d98914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82109 q = 1) (hb : d98800 q = 1) : d98915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82109, d98915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82109, d98915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82110 q = 1) (hb : d98800 q = 1) : d98916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82110, d98916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82110, d98916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d916 q = 1) (hb : d98800 q = 1) : d916 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d917 q = 1) (hb : d98800 q = 1) : d7642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d7642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14029 q ha hb
    | true =>
      simp only [d917, d7642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d918 q = 1) (hb : d98800 q = 1) : d7643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d7643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d918, d7643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d919 q = 1) (hb : d98800 q = 1) : d7644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d7644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d919, d7644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d920 q = 1) (hb : d98800 q = 1) : d7645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d7645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d7645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d922 q = 1) (hb : d98800 q = 1) : d922 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d923 q = 1) (hb : d98800 q = 1) : d7647 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d7647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14030 q ha hb
    | true =>
      simp only [d923, d7647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d924 q = 1) (hb : d98800 q = 1) : d7648 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d7648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d924, d7648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d925 q = 1) (hb : d98800 q = 1) : d7649 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d7649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d925, d7649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6896 q = 1) (hb : d98800 q = 1) : d98919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6896, d98919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14032 q ha hb
    | true =>
      simp only [d6896, d98919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14033 q ha hb
  have h27 (q : Pattern) (ha : d82112 q = 1) (hb : d98800 q = 1) : d98920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82112, d98920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82112, d98920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6181 q = 1) (hb : d98800 q = 1) : d7656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d7656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14031 q ha hb
    | true =>
      simp only [d6181, d7656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6182 q = 1) (hb : d98800 q = 1) : d7657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6182, d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d82113 q = 1) (hb : d98800 q = 1) : d98921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82113, d98921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d82113, d98921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d82114 q = 1) (hb : d98800 q = 1) : d98922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82114, d98922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d82114, d98922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d82115 q = 1) (hb : d98800 q = 1) : d98923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82115, d98923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82115, d98923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d82116 q = 1) (hb : d98800 q = 1) : d98924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82116, d98924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82116, d98924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro14035 (p : Pattern) (ha : d82123 p = 1) (hb : d98800 p = 1) : d98931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6896 q = 1) (hb : d98800 q = 1) : d98919 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6896, d98919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14032 q ha hb
    | true =>
      simp only [d6896, d98919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14033 q ha hb
  have h2 (q : Pattern) (ha : d82112 q = 1) (hb : d98800 q = 1) : d98920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82112, d98920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82112, d98920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6181 q = 1) (hb : d98800 q = 1) : d7656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6181, d7656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14031 q ha hb
    | true =>
      simp only [d6181, d7656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6182 q = 1) (hb : d98800 q = 1) : d7657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6182, d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6182, d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82113 q = 1) (hb : d98800 q = 1) : d98921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82113, d98921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82113, d98921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82121 q = 1) (hb : d98800 q = 1) : d98929 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82121, d98929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82121, d98929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82122 q = 1) (hb : d98800 q = 1) : d98930 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82122, d98930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82122, d98930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82123 q = 1) (hb : d98800 q = 1) : d98931 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82123, d98931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82123, d98931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14036 (p : Pattern) (ha : d6233 p = 1) (hb : d98800 p = 1) : d7706 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d77842 q = 1) : d7682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8227 q ha hb
    | true =>
      simp only [d998, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d77842 q = 1) : d7683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6230 q = 1) (hb : d98800 q = 1) : d7703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6230, d98800, d7703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6230, d98800, d7703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6231 q = 1) (hb : d98800 q = 1) : d7704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6231, d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6231, d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6232 q = 1) (hb : d98800 q = 1) : d7705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6232, d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6232, d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6233 q = 1) (hb : d98800 q = 1) : d7706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6233, d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6233, d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14037 (p : Pattern) (ha : d6923 p = 1) (hb : d92315 p = 1) : d98938 p = 1 := by
  have h0 (q : Pattern) (ha : d6921 q = 1) (hb : d92313 q = 1) : d6921 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6922 q = 1) (hb : d92315 q = 1) : d98937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6922, d92315, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6922, d92315, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6923 q = 1) (hb : d92315 q = 1) : d98938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6923, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6923, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14038 (p : Pattern) (ha : d6929 p = 1) (hb : d98800 p = 1) : d98944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d77842 q = 1) : d7678 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d7678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9870 q ha hb
    | true =>
      simp only [d993, d7678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d77842 q = 1) : d7679 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d7679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d7679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6924 q = 1) (hb : d92315 q = 1) : d98939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6924, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14037 q ha hb
    | true =>
      simp only [d6924, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6925 q = 1) (hb : d92315 q = 1) : d98940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6925, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6925, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6926 q = 1) (hb : d98800 q = 1) : d98941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6926, d98800, d98941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6926, d98800, d98941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6927 q = 1) (hb : d98800 q = 1) : d98942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6927, d98942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6927, d98942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6928 q = 1) (hb : d98800 q = 1) : d98943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6928, d98943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6928, d98943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d6929 q = 1) (hb : d98800 q = 1) : d98944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6929, d98944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6929, d98944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14039 (p : Pattern) (ha : d6933 p = 1) (hb : d98800 p = 1) : d7691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6217 q = 1) (hb : d77842 q = 1) : d7682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6217, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9872 q ha hb
    | true =>
      simp only [d6217, d7682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6218 q = 1) (hb : d77842 q = 1) : d7683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6218, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6218, d7683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1007 q = 1) (hb : d92315 q = 1) : d1007 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6930 q = 1) (hb : d98800 q = 1) : d7688 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6930, d98800, d7688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6930, d98800, d7688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6931 q = 1) (hb : d98800 q = 1) : d7689 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6931, d7689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6931, d7689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6932 q = 1) (hb : d98800 q = 1) : d7690 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6932, d7690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6932, d7690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6933 q = 1) (hb : d98800 q = 1) : d7691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6933, d7691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6933, d7691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14040 (p : Pattern) (ha : d82133 p = 1) (hb : d98800 p = 1) : d98950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6934 q = 1) (hb : d98800 q = 1) : d98945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6934, d98945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14038 q ha hb
    | true =>
      simp only [d6934, d98945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14039 q ha hb
  have h2 (q : Pattern) (ha : d82129 q = 1) (hb : d98800 q = 1) : d98946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82129, d98946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82129, d98946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6234 q = 1) (hb : d98800 q = 1) : d7707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6234, d7707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14036 q ha hb
    | true =>
      simp only [d6234, d7707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6235 q = 1) (hb : d98800 q = 1) : d7708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6235, d7708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6235, d7708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82130 q = 1) (hb : d98800 q = 1) : d98947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82130, d98947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82130, d98947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82131 q = 1) (hb : d98800 q = 1) : d98948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82131, d98948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82131, d98948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82132 q = 1) (hb : d98800 q = 1) : d98949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82132, d98949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82132, d98949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82133 q = 1) (hb : d98800 q = 1) : d98950 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82133, d98950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82133, d98950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14041 (p : Pattern) (ha : d82139 p = 1) (hb : d98800 p = 1) : d98956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d98800 q = 1) : d7588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d7588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d7588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14018 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d98800 q = 1) : d7589 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d7589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d7589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d98800 q = 1) : d7597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d7597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14018 q ha hb
    | true =>
      simp only [d800, d7597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14020 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d98800 q = 1) : d7598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d7598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d7598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d98800 q = 1) : d7599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d7599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d7599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82117 q = 1) (hb : d98800 q = 1) : d98925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82117, d98925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14028 q ha hb
    | true =>
      simp only [d82117, d98925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14034 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d98800 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6909 q = 1) (hb : d98800 q = 1) : d7664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6909, d7664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14022 q ha hb
    | true =>
      simp only [d6909, d7664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82118 q = 1) (hb : d98800 q = 1) : d98926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82118, d98926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82118, d98926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82119 q = 1) (hb : d98800 q = 1) : d98927 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82119, d98927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82119, d98927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d82120 q = 1) (hb : d98800 q = 1) : d98928 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82120, d98928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82120, d98928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d82124 q = 1) (hb : d98800 q = 1) : d98932 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82124, d98932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82124, d98932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14035 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d98800 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d82125 q = 1) (hb : d98800 q = 1) : d98933 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82125, d98933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82125, d98933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82126 q = 1) (hb : d98800 q = 1) : d98934 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82126, d98934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82126, d98934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82127 q = 1) (hb : d98800 q = 1) : d98935 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82127, d98935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82127, d98935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d82128 q = 1) (hb : d98800 q = 1) : d98936 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82128, d98936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82128, d98936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d82134 q = 1) (hb : d98800 q = 1) : d98951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82134, d98951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82134, d98951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14040 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d98800 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d82135 q = 1) (hb : d98800 q = 1) : d98952 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82135, d98952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82135, d98952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d82136 q = 1) (hb : d98800 q = 1) : d98953 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82136, d98953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82136, d98953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82137 q = 1) (hb : d98800 q = 1) : d98954 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82137, d98954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82137, d98954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82138 q = 1) (hb : d98800 q = 1) : d98955 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82138, d98955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82138, d98955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d82139 q = 1) (hb : d98800 q = 1) : d98956 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82139, d98956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82139, d98956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro14042 (p : Pattern) (ha : d82145 p = 1) (hb : d98800 p = 1) : d98962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82140 q = 1) (hb : d98800 q = 1) : d98957 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82140, d98957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82140, d98957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14041 q ha hb
  have h2 (q : Pattern) (ha : d82141 q = 1) (hb : d98800 q = 1) : d98958 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82141, d98958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82141, d98958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82142 q = 1) (hb : d98800 q = 1) : d98959 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82142, d98959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82142, d98959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82143 q = 1) (hb : d98800 q = 1) : d98960 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82143, d98960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82143, d98960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82144 q = 1) (hb : d98800 q = 1) : d98961 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82144, d98961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82144, d98961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82145 q = 1) (hb : d98800 q = 1) : d98962 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82145, d98962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82145, d98962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14043 (p : Pattern) (ha : d1158 p = 1) (hb : d98800 p = 1) : d7734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d98800 q = 1) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d98800 q = 1) : d7732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d98800 q = 1) : d7733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d7733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d7733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1158 q = 1) (hb : d98800 q = 1) : d7734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d7734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d7734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14044 (p : Pattern) (ha : d1168 p = 1) (hb : d98800 p = 1) : d7740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d98800 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1163 q = 1) (hb : d98800 q = 1) : d7735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d7735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14043 q ha hb
    | true =>
      simp only [d1163, d7735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d98800 q = 1) : d7736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d7736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d7736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1165 q = 1) (hb : d98800 q = 1) : d7737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d7737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, d7737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1166 q = 1) (hb : d98800 q = 1) : d7738 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d7738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d7738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1167 q = 1) (hb : d98800 q = 1) : d7739 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d7739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d7739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1168 q = 1) (hb : d98800 q = 1) : d7740 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d7740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d7740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14045 (p : Pattern) (ha : d1171 p = 1) (hb : d98800 p = 1) : d7743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1155 q = 1) (hb : d98800 q = 1) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d98800 q = 1) : d7732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1156, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d98800 q = 1) : d7733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d7733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d7733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1171 q = 1) (hb : d98800 q = 1) : d7743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1171, d7743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1171, d7743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14046 (p : Pattern) (ha : d1178 p = 1) (hb : d98800 p = 1) : d7749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d98800 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1163 q = 1) (hb : d98800 q = 1) : d7735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d7735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14043 q ha hb
    | true =>
      simp only [d1163, d7735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d98800 q = 1) : d7736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d7736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d7736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1165 q = 1) (hb : d98800 q = 1) : d7737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d7737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, d7737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1166 q = 1) (hb : d98800 q = 1) : d7738 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d7738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d7738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1167 q = 1) (hb : d98800 q = 1) : d7739 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d7739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d7739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d98800 q = 1) : d1172 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1173 q = 1) (hb : d98800 q = 1) : d7744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d7744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14045 q ha hb
    | true =>
      simp only [d1173, d7744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1174 q = 1) (hb : d98800 q = 1) : d7745 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d7745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d7745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1175 q = 1) (hb : d98800 q = 1) : d7746 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d7746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1175, d7746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1176 q = 1) (hb : d98800 q = 1) : d7747 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d7747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d7747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1177 q = 1) (hb : d98800 q = 1) : d7748 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d7748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d7748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1178 q = 1) (hb : d98800 q = 1) : d7749 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d7749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1178, d7749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro14047 (p : Pattern) (ha : d6966 p = 1) (hb : d98800 p = 1) : d7734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5030 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9882 q ha hb
    | true =>
      simp only [d5030, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5031 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5031, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6963 q = 1) (hb : d98800 q = 1) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6963, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6963, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6964 q = 1) (hb : d98800 q = 1) : d7732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6964, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6964, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6965 q = 1) (hb : d98800 q = 1) : d7733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6965, d7733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6965, d7733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6966 q = 1) (hb : d98800 q = 1) : d7734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6966, d7734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6966, d7734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14048 (p : Pattern) (ha : d6987 p = 1) (hb : d98800 p = 1) : d7816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d98800 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6982 q = 1) (hb : d98800 q = 1) : d7735 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6982, d7735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14047 q ha hb
    | true =>
      simp only [d6982, d7735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6983 q = 1) (hb : d98800 q = 1) : d7736 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6983, d7736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6983, d7736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6984 q = 1) (hb : d98800 q = 1) : d7737 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d6984, d7737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6984, d7737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d6985 q = 1) (hb : d98800 q = 1) : d7738 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d6985, d7738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6985, d7738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6986 q = 1) (hb : d98800 q = 1) : d7739 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d6986, d7739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6986, d7739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d98800 q = 1) : d1354 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6987 q = 1) (hb : d98800 q = 1) : d7816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d6987, d7816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6987, d7816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14049 (p : Pattern) (ha : d1183 p = 1) (hb : d98800 p = 1) : d7754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d98800 q = 1) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d98800 q = 1) : d7732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d98800 q = 1) : d7753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d7753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d7753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1183 q = 1) (hb : d98800 q = 1) : d7754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, d7754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, d7754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14050 (p : Pattern) (ha : d1192 p = 1) (hb : d98800 p = 1) : d7761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d98800 q = 1) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d98800 q = 1) : d7759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d7759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d7759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d98800 q = 1) : d7760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d7760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d7760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1192 q = 1) (hb : d98800 q = 1) : d7761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, d7761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, d7761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14051 (p : Pattern) (ha : d6257 p = 1) (hb : d98800 p = 1) : d7787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6254 q = 1) (hb : d98800 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d98800, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6254, d98800, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d98800 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6256 q = 1) (hb : d98800 q = 1) : d7786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6256, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6257 q = 1) (hb : d98800 q = 1) : d7787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6257, d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6257, d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14052 (p : Pattern) (ha : d6956 p = 1) (hb : d92315 p = 1) : d98966 p = 1 := by
  have h0 (q : Pattern) (ha : d6954 q = 1) (hb : d92313 q = 1) : d6954 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6955 q = 1) (hb : d92315 q = 1) : d98965 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6955, d92315, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6955, d92315, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6956 q = 1) (hb : d92315 q = 1) : d98966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6956, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6956, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14053 (p : Pattern) (ha : d6962 p = 1) (hb : d98800 p = 1) : d98972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1222 q = 1) (hb : d77842 q = 1) : d7767 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d7767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9887 q ha hb
    | true =>
      simp only [d1222, d7767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1223 q = 1) (hb : d77842 q = 1) : d7768 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d7768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1223, d7768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6957 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14052 q ha hb
    | true =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6958 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6959 q = 1) (hb : d98800 q = 1) : d98969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6959, d98800, d98969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6959, d98800, d98969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6960 q = 1) (hb : d98800 q = 1) : d98970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6960, d98970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6960, d98970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d6961 q = 1) (hb : d98800 q = 1) : d98971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6961, d98971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6961, d98971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6962 q = 1) (hb : d98800 q = 1) : d98972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6962, d98972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6962, d98972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14054 (p : Pattern) (ha : d82152 p = 1) (hb : d98800 p = 1) : d98978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d98800 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1186 q = 1) (hb : d98800 q = 1) : d7755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d7755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14049 q ha hb
    | true =>
      simp only [d1186, d7755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d98800 q = 1) : d7756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d7756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d7756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1188 q = 1) (hb : d98800 q = 1) : d7757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d7757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, d7757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1189 q = 1) (hb : d98800 q = 1) : d7758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d7758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d7758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d98800 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1196 q = 1) (hb : d98800 q = 1) : d7762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d7762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14050 q ha hb
    | true =>
      simp only [d1196, d7762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1197 q = 1) (hb : d98800 q = 1) : d7763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d7763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d7763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1198 q = 1) (hb : d98800 q = 1) : d7764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d7764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1198, d7764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6967 q = 1) (hb : d98800 q = 1) : d98973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6967, d98973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14053 q ha hb
    | true =>
      simp only [d6967, d98973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14047 q ha hb
  have h11 (q : Pattern) (ha : d82148 q = 1) (hb : d98800 q = 1) : d98974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82148, d98974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82148, d98974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6299 q = 1) (hb : d98800 q = 1) : d7788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d7788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14051 q ha hb
    | true =>
      simp only [d6299, d7788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6300 q = 1) (hb : d98800 q = 1) : d7789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6300, d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82149 q = 1) (hb : d98800 q = 1) : d98975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82149, d98975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82149, d98975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82150 q = 1) (hb : d98800 q = 1) : d98976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82150, d98976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82150, d98976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82151 q = 1) (hb : d98800 q = 1) : d98977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82151, d98977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82151, d98977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82152 q = 1) (hb : d98800 q = 1) : d98978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82152, d98978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82152, d98978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro14055 (p : Pattern) (ha : d1326 p = 1) (hb : d98800 p = 1) : d7794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d98800 q = 1) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d98800 q = 1) : d7732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d98800 q = 1) : d7753 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d7753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d7753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1326 q = 1) (hb : d98800 q = 1) : d7794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1326, d7794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1326, d7794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14056 (p : Pattern) (ha : d1332 p = 1) (hb : d98800 p = 1) : d7799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d98800 q = 1) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1155, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d98800 q = 1) : d7759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d7759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d7759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d98800 q = 1) : d7760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d7760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d7760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1332 q = 1) (hb : d98800 q = 1) : d7799 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1332, d7799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1332, d7799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14057 (p : Pattern) (ha : d6266 p = 1) (hb : d98800 p = 1) : d7808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8247 q ha hb
    | true =>
      simp only [d1149, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6254 q = 1) (hb : d98800 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6254, d98800, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6254, d98800, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6255 q = 1) (hb : d98800 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6255, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6256 q = 1) (hb : d98800 q = 1) : d7786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6256, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6256, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6266 q = 1) (hb : d98800 q = 1) : d7808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6266, d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6266, d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14058 (p : Pattern) (ha : d6973 p = 1) (hb : d98800 p = 1) : d98979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d77842 q = 1) : d7767 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d7767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9887 q ha hb
    | true =>
      simp only [d1222, d7767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d77842 q = 1) : d7768 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d7768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d7768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6957 q = 1) (hb : d92315 q = 1) : d98967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14052 q ha hb
    | true =>
      simp only [d6957, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d6958 q = 1) (hb : d92315 q = 1) : d98968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6958, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6959 q = 1) (hb : d98800 q = 1) : d98969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6959, d98800, d98969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6959, d98800, d98969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6960 q = 1) (hb : d98800 q = 1) : d98970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6960, d98970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6960, d98970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6961 q = 1) (hb : d98800 q = 1) : d98971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6961, d98971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d6961, d98971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d6973 q = 1) (hb : d98800 q = 1) : d98979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6973, d98979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d6973, d98979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14059 (p : Pattern) (ha : d6974 p = 1) (hb : d98800 p = 1) : d7743 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5030 q = 1) (hb : d77842 q = 1) : d7729 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5030, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9882 q ha hb
    | true =>
      simp only [d5030, d7729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5031 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5031, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5031, d7730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d92315 q = 1) : d1154 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6963 q = 1) (hb : d98800 q = 1) : d7731 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6963, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6963, d98800, d7731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6964 q = 1) (hb : d98800 q = 1) : d7732 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6964, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6964, d7732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6965 q = 1) (hb : d98800 q = 1) : d7733 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6965, d7733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6965, d7733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6974 q = 1) (hb : d98800 q = 1) : d7743 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6974, d7743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6974, d7743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14060 (p : Pattern) (ha : d82157 p = 1) (hb : d98800 p = 1) : d98985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d98800 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1186 q = 1) (hb : d98800 q = 1) : d7755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d7755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14049 q ha hb
    | true =>
      simp only [d1186, d7755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d98800 q = 1) : d7756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d7756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d7756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1188 q = 1) (hb : d98800 q = 1) : d7757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d7757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, d7757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1189 q = 1) (hb : d98800 q = 1) : d7758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d7758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d7758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d98800 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1196 q = 1) (hb : d98800 q = 1) : d7762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d7762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14050 q ha hb
    | true =>
      simp only [d1196, d7762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1197 q = 1) (hb : d98800 q = 1) : d7763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d7763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d7763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1198 q = 1) (hb : d98800 q = 1) : d7764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d7764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1198, d7764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d6967 q = 1) (hb : d98800 q = 1) : d98973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6967, d98973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14053 q ha hb
    | true =>
      simp only [d6967, d98973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14047 q ha hb
  have h11 (q : Pattern) (ha : d82148 q = 1) (hb : d98800 q = 1) : d98974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82148, d98974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82148, d98974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6299 q = 1) (hb : d98800 q = 1) : d7788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6299, d7788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14051 q ha hb
    | true =>
      simp only [d6299, d7788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6300 q = 1) (hb : d98800 q = 1) : d7789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6300, d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6300, d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82149 q = 1) (hb : d98800 q = 1) : d98975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82149, d98975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82149, d98975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82150 q = 1) (hb : d98800 q = 1) : d98976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82150, d98976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82150, d98976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82151 q = 1) (hb : d98800 q = 1) : d98977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82151, d98977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82151, d98977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1327 q = 1) (hb : d98800 q = 1) : d1327 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1328 q = 1) (hb : d98800 q = 1) : d7795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d7795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14055 q ha hb
    | true =>
      simp only [d1328, d7795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1329 q = 1) (hb : d98800 q = 1) : d7796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d7796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d7796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1330 q = 1) (hb : d98800 q = 1) : d7797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d7797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1330, d7797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d1331 q = 1) (hb : d98800 q = 1) : d7798 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d7798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d7798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1333 q = 1) (hb : d98800 q = 1) : d1333 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d1334 q = 1) (hb : d98800 q = 1) : d7800 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d7800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14056 q ha hb
    | true =>
      simp only [d1334, d7800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d1335 q = 1) (hb : d98800 q = 1) : d7801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d7801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d7801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1336 q = 1) (hb : d98800 q = 1) : d7802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d7802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d1336, d7802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d6975 q = 1) (hb : d98800 q = 1) : d98980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6975, d98980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14058 q ha hb
    | true =>
      simp only [d6975, d98980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14059 q ha hb
  have h27 (q : Pattern) (ha : d82153 q = 1) (hb : d98800 q = 1) : d98981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82153, d98981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82153, d98981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6320 q = 1) (hb : d98800 q = 1) : d7809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d7809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14057 q ha hb
    | true =>
      simp only [d6320, d7809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6321 q = 1) (hb : d98800 q = 1) : d7810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6321, d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d82154 q = 1) (hb : d98800 q = 1) : d98982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82154, d98982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d82154, d98982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d82155 q = 1) (hb : d98800 q = 1) : d98983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82155, d98983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d82155, d98983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d82156 q = 1) (hb : d98800 q = 1) : d98984 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82156, d98984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82156, d98984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d82157 q = 1) (hb : d98800 q = 1) : d98985 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82157, d98985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82157, d98985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro14061 (p : Pattern) (ha : d82164 p = 1) (hb : d98800 p = 1) : d98992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6975 q = 1) (hb : d98800 q = 1) : d98980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6975, d98980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14058 q ha hb
    | true =>
      simp only [d6975, d98980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14059 q ha hb
  have h2 (q : Pattern) (ha : d82153 q = 1) (hb : d98800 q = 1) : d98981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82153, d98981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82153, d98981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6320 q = 1) (hb : d98800 q = 1) : d7809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6320, d7809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14057 q ha hb
    | true =>
      simp only [d6320, d7809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6321 q = 1) (hb : d98800 q = 1) : d7810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6321, d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6321, d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82154 q = 1) (hb : d98800 q = 1) : d98982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82154, d98982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82154, d98982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82162 q = 1) (hb : d98800 q = 1) : d98990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82162, d98990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82162, d98990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82163 q = 1) (hb : d98800 q = 1) : d98991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82163, d98991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82163, d98991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82164 q = 1) (hb : d98800 q = 1) : d98992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82164, d98992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82164, d98992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14062 (p : Pattern) (ha : d6378 p = 1) (hb : d98800 p = 1) : d7859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d77842 q = 1) : d7835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8255 q ha hb
    | true =>
      simp only [d1423, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d77842 q = 1) : d7836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6375 q = 1) (hb : d98800 q = 1) : d7856 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6375, d98800, d7856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6375, d98800, d7856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6376 q = 1) (hb : d98800 q = 1) : d7857 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6376, d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6376, d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6377 q = 1) (hb : d98800 q = 1) : d7858 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6377, d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6377, d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6378 q = 1) (hb : d98800 q = 1) : d7859 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6378, d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6378, d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14063 (p : Pattern) (ha : d7002 p = 1) (hb : d92315 p = 1) : d98999 p = 1 := by
  have h0 (q : Pattern) (ha : d7000 q = 1) (hb : d92313 q = 1) : d7000 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7001 q = 1) (hb : d92315 q = 1) : d98998 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7001, d92315, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7001, d92315, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7002 q = 1) (hb : d92315 q = 1) : d98999 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7002, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7002, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14064 (p : Pattern) (ha : d7008 p = 1) (hb : d98800 p = 1) : d99005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d77842 q = 1) : d7831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d7831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9896 q ha hb
    | true =>
      simp only [d1418, d7831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d77842 q = 1) : d7832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d7832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d7832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7003 q = 1) (hb : d92315 q = 1) : d99000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7003, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14063 q ha hb
    | true =>
      simp only [d7003, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7004 q = 1) (hb : d92315 q = 1) : d99001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7004, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7004, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7005 q = 1) (hb : d98800 q = 1) : d99002 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7005, d98800, d99002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7005, d98800, d99002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7006 q = 1) (hb : d98800 q = 1) : d99003 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7006, d99003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7006, d99003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7007 q = 1) (hb : d98800 q = 1) : d99004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7007, d99004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7007, d99004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d7008 q = 1) (hb : d98800 q = 1) : d99005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7008, d99005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7008, d99005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14065 (p : Pattern) (ha : d7012 p = 1) (hb : d98800 p = 1) : d7844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6362 q = 1) (hb : d77842 q = 1) : d7835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6362, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9898 q ha hb
    | true =>
      simp only [d6362, d7835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6363 q = 1) (hb : d77842 q = 1) : d7836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6363, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6363, d7836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1432 q = 1) (hb : d92315 q = 1) : d1432 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7009 q = 1) (hb : d98800 q = 1) : d7841 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7009, d98800, d7841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7009, d98800, d7841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7010 q = 1) (hb : d98800 q = 1) : d7842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7010, d7842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7010, d7842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7011 q = 1) (hb : d98800 q = 1) : d7843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7011, d7843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7011, d7843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d7012 q = 1) (hb : d98800 q = 1) : d7844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7012, d7844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7012, d7844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14066 (p : Pattern) (ha : d82174 p = 1) (hb : d98800 p = 1) : d99011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7013 q = 1) (hb : d98800 q = 1) : d99006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7013, d99006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14064 q ha hb
    | true =>
      simp only [d7013, d99006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14065 q ha hb
  have h2 (q : Pattern) (ha : d82170 q = 1) (hb : d98800 q = 1) : d99007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82170, d99007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82170, d99007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6379 q = 1) (hb : d98800 q = 1) : d7860 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6379, d7860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14062 q ha hb
    | true =>
      simp only [d6379, d7860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6380 q = 1) (hb : d98800 q = 1) : d7861 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6380, d7861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6380, d7861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82171 q = 1) (hb : d98800 q = 1) : d99008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82171, d99008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82171, d99008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82172 q = 1) (hb : d98800 q = 1) : d99009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82172, d99009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82172, d99009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82173 q = 1) (hb : d98800 q = 1) : d99010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82173, d99010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82173, d99010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82174 q = 1) (hb : d98800 q = 1) : d99011 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82174, d99011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82174, d99011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14067 (p : Pattern) (ha : d82180 p = 1) (hb : d98800 p = 1) : d99017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d98800 q = 1) : d7741 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d7741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d7741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14044 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d98800 q = 1) : d7742 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d7742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d7742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d98800 q = 1) : d7750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d7750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14044 q ha hb
    | true =>
      simp only [d1179, d7750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14046 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d98800 q = 1) : d7751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d7751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d7751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d98800 q = 1) : d7752 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d7752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d7752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82158 q = 1) (hb : d98800 q = 1) : d98986 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82158, d98986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14054 q ha hb
    | true =>
      simp only [d82158, d98986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14060 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d98800 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6988 q = 1) (hb : d98800 q = 1) : d7817 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d6988, d7817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14048 q ha hb
    | true =>
      simp only [d6988, d7817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82159 q = 1) (hb : d98800 q = 1) : d98987 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82159, d98987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82159, d98987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82160 q = 1) (hb : d98800 q = 1) : d98988 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82160, d98988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82160, d98988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d82161 q = 1) (hb : d98800 q = 1) : d98989 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82161, d98989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82161, d98989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d82165 q = 1) (hb : d98800 q = 1) : d98993 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82165, d98993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82165, d98993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14061 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d98800 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d82166 q = 1) (hb : d98800 q = 1) : d98994 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82166, d98994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82166, d98994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82167 q = 1) (hb : d98800 q = 1) : d98995 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82167, d98995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82167, d98995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82168 q = 1) (hb : d98800 q = 1) : d98996 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82168, d98996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82168, d98996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d82169 q = 1) (hb : d98800 q = 1) : d98997 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82169, d98997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82169, d98997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d82175 q = 1) (hb : d98800 q = 1) : d99012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82175, d99012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82175, d99012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14066 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d98800 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d82176 q = 1) (hb : d98800 q = 1) : d99013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82176, d99013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82176, d99013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d82177 q = 1) (hb : d98800 q = 1) : d99014 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82177, d99014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82177, d99014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82178 q = 1) (hb : d98800 q = 1) : d99015 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82178, d99015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82178, d99015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82179 q = 1) (hb : d98800 q = 1) : d99016 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82179, d99016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82179, d99016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d82180 q = 1) (hb : d98800 q = 1) : d99017 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82180, d99017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82180, d99017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro14068 (p : Pattern) (ha : d82186 p = 1) (hb : d98800 p = 1) : d99023 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82181 q = 1) (hb : d98800 q = 1) : d99018 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82181, d99018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82181, d99018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14067 q ha hb
  have h2 (q : Pattern) (ha : d82182 q = 1) (hb : d98800 q = 1) : d99019 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82182, d99019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82182, d99019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82183 q = 1) (hb : d98800 q = 1) : d99020 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82183, d99020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82183, d99020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82184 q = 1) (hb : d98800 q = 1) : d99021 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82184, d99021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82184, d99021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82185 q = 1) (hb : d98800 q = 1) : d99022 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82185, d99022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82185, d99022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82186 q = 1) (hb : d98800 q = 1) : d99023 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82186, d99023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82186, d99023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14069 (p : Pattern) (ha : d1619 p = 1) (hb : d98800 p = 1) : d7888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d98800 q = 1) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d98800 q = 1) : d7886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d98800 q = 1) : d7887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d7887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d7887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1619 q = 1) (hb : d98800 q = 1) : d7888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d7888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d7888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14070 (p : Pattern) (ha : d1629 p = 1) (hb : d98800 p = 1) : d7894 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d98800 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1624 q = 1) (hb : d98800 q = 1) : d7889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d7889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14069 q ha hb
    | true =>
      simp only [d1624, d7889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d98800 q = 1) : d7890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d7890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d7890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1626 q = 1) (hb : d98800 q = 1) : d7891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d7891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, d7891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1627 q = 1) (hb : d98800 q = 1) : d7892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d7892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d7892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1628 q = 1) (hb : d98800 q = 1) : d7893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d7893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d7893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1629 q = 1) (hb : d98800 q = 1) : d7894 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d7894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d7894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14071 (p : Pattern) (ha : d1632 p = 1) (hb : d98800 p = 1) : d7897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1616 q = 1) (hb : d98800 q = 1) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d98800 q = 1) : d7886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1617, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d98800 q = 1) : d7887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d7887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d7887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d1632 q = 1) (hb : d98800 q = 1) : d7897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1632, d7897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1632, d7897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14072 (p : Pattern) (ha : d1639 p = 1) (hb : d98800 p = 1) : d7903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d98800 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1624 q = 1) (hb : d98800 q = 1) : d7889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d7889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14069 q ha hb
    | true =>
      simp only [d1624, d7889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d98800 q = 1) : d7890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d7890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d7890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1626 q = 1) (hb : d98800 q = 1) : d7891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d7891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, d7891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1627 q = 1) (hb : d98800 q = 1) : d7892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d7892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d7892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1628 q = 1) (hb : d98800 q = 1) : d7893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d7893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d7893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d98800 q = 1) : d1633 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1634 q = 1) (hb : d98800 q = 1) : d7898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d7898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14071 q ha hb
    | true =>
      simp only [d1634, d7898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1635 q = 1) (hb : d98800 q = 1) : d7899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d7899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d7899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1636 q = 1) (hb : d98800 q = 1) : d7900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d7900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1636, d7900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1637 q = 1) (hb : d98800 q = 1) : d7901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d7901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d7901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1638 q = 1) (hb : d98800 q = 1) : d7902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d7902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d7902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1639 q = 1) (hb : d98800 q = 1) : d7903 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d7903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1639, d7903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro14073 (p : Pattern) (ha : d7046 p = 1) (hb : d98800 p = 1) : d7888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5146 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9908 q ha hb
    | true =>
      simp only [d5146, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5147 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5147, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7043 q = 1) (hb : d98800 q = 1) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7043, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7043, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7044 q = 1) (hb : d98800 q = 1) : d7886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7044, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7044, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7045 q = 1) (hb : d98800 q = 1) : d7887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7045, d7887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7045, d7887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7046 q = 1) (hb : d98800 q = 1) : d7888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7046, d7888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7046, d7888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14074 (p : Pattern) (ha : d7067 p = 1) (hb : d98800 p = 1) : d7970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d98800 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7062 q = 1) (hb : d98800 q = 1) : d7889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7062, d7889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14073 q ha hb
    | true =>
      simp only [d7062, d7889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7063 q = 1) (hb : d98800 q = 1) : d7890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7063, d7890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7063, d7890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7064 q = 1) (hb : d98800 q = 1) : d7891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7064, d7891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7064, d7891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7065 q = 1) (hb : d98800 q = 1) : d7892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7065, d7892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7065, d7892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7066 q = 1) (hb : d98800 q = 1) : d7893 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7066, d7893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7066, d7893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d98800 q = 1) : d1831 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7067 q = 1) (hb : d98800 q = 1) : d7970 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7067, d7970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7067, d7970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14075 (p : Pattern) (ha : d1644 p = 1) (hb : d98800 p = 1) : d7908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d98800 q = 1) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d98800 q = 1) : d7886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d98800 q = 1) : d7907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d7907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d7907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1644 q = 1) (hb : d98800 q = 1) : d7908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, d7908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, d7908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14076 (p : Pattern) (ha : d1653 p = 1) (hb : d98800 p = 1) : d7915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d98800 q = 1) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d98800 q = 1) : d7913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d7913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d7913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d98800 q = 1) : d7914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d7914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d7914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1653 q = 1) (hb : d98800 q = 1) : d7915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, d7915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, d7915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14077 (p : Pattern) (ha : d6403 p = 1) (hb : d98800 p = 1) : d7941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6400 q = 1) (hb : d98800 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d98800, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6400, d98800, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d98800 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6402 q = 1) (hb : d98800 q = 1) : d7940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6402, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6403 q = 1) (hb : d98800 q = 1) : d7941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6403, d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6403, d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14078 (p : Pattern) (ha : d7036 p = 1) (hb : d92315 p = 1) : d99028 p = 1 := by
  have h0 (q : Pattern) (ha : d7034 q = 1) (hb : d92313 q = 1) : d7034 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7035 q = 1) (hb : d92315 q = 1) : d99027 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7035, d92315, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7035, d92315, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7036 q = 1) (hb : d92315 q = 1) : d99028 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7036, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7036, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14079 (p : Pattern) (ha : d7042 p = 1) (hb : d98800 p = 1) : d99034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1677 q = 1) (hb : d77842 q = 1) : d7921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d7921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9913 q ha hb
    | true =>
      simp only [d1677, d7921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1678 q = 1) (hb : d77842 q = 1) : d7922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d7922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1678, d7922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7037 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14078 q ha hb
    | true =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7038 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7039 q = 1) (hb : d98800 q = 1) : d99031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7039, d98800, d99031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7039, d98800, d99031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7040 q = 1) (hb : d98800 q = 1) : d99032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7040, d99032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7040, d99032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7041 q = 1) (hb : d98800 q = 1) : d99033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7041, d99033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7041, d99033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7042 q = 1) (hb : d98800 q = 1) : d99034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7042, d99034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7042, d99034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14080 (p : Pattern) (ha : d82194 p = 1) (hb : d98800 p = 1) : d99040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d98800 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1647 q = 1) (hb : d98800 q = 1) : d7909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d7909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14075 q ha hb
    | true =>
      simp only [d1647, d7909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d98800 q = 1) : d7910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d7910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d7910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1649 q = 1) (hb : d98800 q = 1) : d7911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d7911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, d7911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1650 q = 1) (hb : d98800 q = 1) : d7912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d7912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d7912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d98800 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1657 q = 1) (hb : d98800 q = 1) : d7916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d7916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14076 q ha hb
    | true =>
      simp only [d1657, d7916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1658 q = 1) (hb : d98800 q = 1) : d7917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d7917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d7917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1659 q = 1) (hb : d98800 q = 1) : d7918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d7918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1659, d7918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7047 q = 1) (hb : d98800 q = 1) : d99035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7047, d99035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14079 q ha hb
    | true =>
      simp only [d7047, d99035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14073 q ha hb
  have h11 (q : Pattern) (ha : d82190 q = 1) (hb : d98800 q = 1) : d99036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82190, d99036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82190, d99036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6445 q = 1) (hb : d98800 q = 1) : d7942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d7942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14077 q ha hb
    | true =>
      simp only [d6445, d7942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6446 q = 1) (hb : d98800 q = 1) : d7943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6446, d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82191 q = 1) (hb : d98800 q = 1) : d99037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82191, d99037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82191, d99037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82192 q = 1) (hb : d98800 q = 1) : d99038 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82192, d99038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82192, d99038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82193 q = 1) (hb : d98800 q = 1) : d99039 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82193, d99039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82193, d99039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82194 q = 1) (hb : d98800 q = 1) : d99040 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82194, d99040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82194, d99040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro14081 (p : Pattern) (ha : d1803 p = 1) (hb : d98800 p = 1) : d7948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d98800 q = 1) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d98800 q = 1) : d7886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d98800 q = 1) : d7907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d7907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d7907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1803 q = 1) (hb : d98800 q = 1) : d7948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1803, d7948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1803, d7948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14082 (p : Pattern) (ha : d1809 p = 1) (hb : d98800 p = 1) : d7953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d98800 q = 1) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1616, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d98800 q = 1) : d7913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d7913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d7913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d98800 q = 1) : d7914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d7914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d7914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1809 q = 1) (hb : d98800 q = 1) : d7953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1809, d7953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1809, d7953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14083 (p : Pattern) (ha : d6412 p = 1) (hb : d98800 p = 1) : d7962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8275 q ha hb
    | true =>
      simp only [d1610, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6400 q = 1) (hb : d98800 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6400, d98800, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6400, d98800, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6401 q = 1) (hb : d98800 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6401, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6402 q = 1) (hb : d98800 q = 1) : d7940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6402, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6402, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6412 q = 1) (hb : d98800 q = 1) : d7962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6412, d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6412, d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14084 (p : Pattern) (ha : d7053 p = 1) (hb : d98800 p = 1) : d99041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d77842 q = 1) : d7921 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d7921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9913 q ha hb
    | true =>
      simp only [d1677, d7921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d77842 q = 1) : d7922 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d7922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d7922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7037 q = 1) (hb : d92315 q = 1) : d99029 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14078 q ha hb
    | true =>
      simp only [d7037, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7038 q = 1) (hb : d92315 q = 1) : d99030 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7038, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7039 q = 1) (hb : d98800 q = 1) : d99031 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7039, d98800, d99031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7039, d98800, d99031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7040 q = 1) (hb : d98800 q = 1) : d99032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7040, d99032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7040, d99032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7041 q = 1) (hb : d98800 q = 1) : d99033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7041, d99033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7041, d99033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d7053 q = 1) (hb : d98800 q = 1) : d99041 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7053, d99041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7053, d99041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14085 (p : Pattern) (ha : d7054 p = 1) (hb : d98800 p = 1) : d7897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5146 q = 1) (hb : d77842 q = 1) : d7883 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5146, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9908 q ha hb
    | true =>
      simp only [d5146, d7883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5147 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5147, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5147, d7884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d92315 q = 1) : d1615 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7043 q = 1) (hb : d98800 q = 1) : d7885 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7043, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7043, d98800, d7885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7044 q = 1) (hb : d98800 q = 1) : d7886 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7044, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7044, d7886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7045 q = 1) (hb : d98800 q = 1) : d7887 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7045, d7887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7045, d7887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d7054 q = 1) (hb : d98800 q = 1) : d7897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7054, d7897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7054, d7897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14086 (p : Pattern) (ha : d82199 p = 1) (hb : d98800 p = 1) : d99047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d98800 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1647 q = 1) (hb : d98800 q = 1) : d7909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d7909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14075 q ha hb
    | true =>
      simp only [d1647, d7909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d98800 q = 1) : d7910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d7910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d7910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1649 q = 1) (hb : d98800 q = 1) : d7911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d7911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, d7911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1650 q = 1) (hb : d98800 q = 1) : d7912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d7912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d7912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d98800 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1657 q = 1) (hb : d98800 q = 1) : d7916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d7916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14076 q ha hb
    | true =>
      simp only [d1657, d7916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1658 q = 1) (hb : d98800 q = 1) : d7917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d7917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d7917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1659 q = 1) (hb : d98800 q = 1) : d7918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d7918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1659, d7918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7047 q = 1) (hb : d98800 q = 1) : d99035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7047, d99035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14079 q ha hb
    | true =>
      simp only [d7047, d99035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14073 q ha hb
  have h11 (q : Pattern) (ha : d82190 q = 1) (hb : d98800 q = 1) : d99036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82190, d99036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82190, d99036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6445 q = 1) (hb : d98800 q = 1) : d7942 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6445, d7942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14077 q ha hb
    | true =>
      simp only [d6445, d7942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6446 q = 1) (hb : d98800 q = 1) : d7943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6446, d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6446, d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82191 q = 1) (hb : d98800 q = 1) : d99037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82191, d99037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82191, d99037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82192 q = 1) (hb : d98800 q = 1) : d99038 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82192, d99038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82192, d99038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82193 q = 1) (hb : d98800 q = 1) : d99039 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82193, d99039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82193, d99039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1804 q = 1) (hb : d98800 q = 1) : d1804 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1805 q = 1) (hb : d98800 q = 1) : d7949 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d7949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14081 q ha hb
    | true =>
      simp only [d1805, d7949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1806 q = 1) (hb : d98800 q = 1) : d7950 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d7950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d7950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1807 q = 1) (hb : d98800 q = 1) : d7951 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d7951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1807, d7951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d1808 q = 1) (hb : d98800 q = 1) : d7952 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d7952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d7952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d1810 q = 1) (hb : d98800 q = 1) : d1810 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d1811 q = 1) (hb : d98800 q = 1) : d7954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d7954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14082 q ha hb
    | true =>
      simp only [d1811, d7954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d1812 q = 1) (hb : d98800 q = 1) : d7955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d7955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d7955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d1813 q = 1) (hb : d98800 q = 1) : d7956 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d7956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d1813, d7956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7055 q = 1) (hb : d98800 q = 1) : d99042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7055, d99042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14084 q ha hb
    | true =>
      simp only [d7055, d99042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14085 q ha hb
  have h27 (q : Pattern) (ha : d82195 q = 1) (hb : d98800 q = 1) : d99043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82195, d99043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82195, d99043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6466 q = 1) (hb : d98800 q = 1) : d7963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d7963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14083 q ha hb
    | true =>
      simp only [d6466, d7963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6467 q = 1) (hb : d98800 q = 1) : d7964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6467, d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d82196 q = 1) (hb : d98800 q = 1) : d99044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82196, d99044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d82196, d99044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d82197 q = 1) (hb : d98800 q = 1) : d99045 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82197, d99045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d82197, d99045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d82198 q = 1) (hb : d98800 q = 1) : d99046 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82198, d99046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82198, d99046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d82199 q = 1) (hb : d98800 q = 1) : d99047 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82199, d99047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82199, d99047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro14087 (p : Pattern) (ha : d82206 p = 1) (hb : d98800 p = 1) : d99054 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7055 q = 1) (hb : d98800 q = 1) : d99042 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7055, d99042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14084 q ha hb
    | true =>
      simp only [d7055, d99042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14085 q ha hb
  have h2 (q : Pattern) (ha : d82195 q = 1) (hb : d98800 q = 1) : d99043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82195, d99043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82195, d99043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6466 q = 1) (hb : d98800 q = 1) : d7963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6466, d7963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14083 q ha hb
    | true =>
      simp only [d6466, d7963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6467 q = 1) (hb : d98800 q = 1) : d7964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6467, d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6467, d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82196 q = 1) (hb : d98800 q = 1) : d99044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82196, d99044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82196, d99044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82204 q = 1) (hb : d98800 q = 1) : d99052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82204, d99052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82204, d99052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82205 q = 1) (hb : d98800 q = 1) : d99053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82205, d99053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82205, d99053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82206 q = 1) (hb : d98800 q = 1) : d99054 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82206, d99054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82206, d99054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14088 (p : Pattern) (ha : d6524 p = 1) (hb : d98800 p = 1) : d8013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d77842 q = 1) : d7989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8283 q ha hb
    | true =>
      simp only [d1900, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d77842 q = 1) : d7990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6521 q = 1) (hb : d98800 q = 1) : d8010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6521, d98800, d8010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6521, d98800, d8010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6522 q = 1) (hb : d98800 q = 1) : d8011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6522, d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6522, d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6523 q = 1) (hb : d98800 q = 1) : d8012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6523, d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6523, d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6524 q = 1) (hb : d98800 q = 1) : d8013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6524, d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6524, d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14089 (p : Pattern) (ha : d7082 p = 1) (hb : d92315 p = 1) : d99061 p = 1 := by
  have h0 (q : Pattern) (ha : d7080 q = 1) (hb : d92313 q = 1) : d7080 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6505 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7081 q = 1) (hb : d92315 q = 1) : d99060 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7081, d92315, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7081, d92315, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7082 q = 1) (hb : d92315 q = 1) : d99061 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7082, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7082, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14090 (p : Pattern) (ha : d7088 p = 1) (hb : d98800 p = 1) : d99067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d77842 q = 1) : d7985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d7985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9922 q ha hb
    | true =>
      simp only [d1895, d7985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d77842 q = 1) : d7986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d7986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d7986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7083 q = 1) (hb : d92315 q = 1) : d99062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7083, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14089 q ha hb
    | true =>
      simp only [d7083, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7084 q = 1) (hb : d92315 q = 1) : d99063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7084, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7084, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7085 q = 1) (hb : d98800 q = 1) : d99064 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7085, d98800, d99064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7085, d98800, d99064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7086 q = 1) (hb : d98800 q = 1) : d99065 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7086, d99065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7086, d99065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7087 q = 1) (hb : d98800 q = 1) : d99066 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7087, d99066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7087, d99066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d7088 q = 1) (hb : d98800 q = 1) : d99067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7088, d99067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7088, d99067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14091 (p : Pattern) (ha : d7092 p = 1) (hb : d98800 p = 1) : d7998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6508 q = 1) (hb : d77842 q = 1) : d7989 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6508, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9924 q ha hb
    | true =>
      simp only [d6508, d7989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6509 q = 1) (hb : d77842 q = 1) : d7990 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6509, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6509, d7990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1909 q = 1) (hb : d92315 q = 1) : d1909 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7089 q = 1) (hb : d98800 q = 1) : d7995 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7089, d98800, d7995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7089, d98800, d7995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7090 q = 1) (hb : d98800 q = 1) : d7996 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7090, d7996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7090, d7996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7091 q = 1) (hb : d98800 q = 1) : d7997 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7091, d7997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7091, d7997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d7092 q = 1) (hb : d98800 q = 1) : d7998 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7092, d7998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7092, d7998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14092 (p : Pattern) (ha : d82216 p = 1) (hb : d98800 p = 1) : d99073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7093 q = 1) (hb : d98800 q = 1) : d99068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7093, d99068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14090 q ha hb
    | true =>
      simp only [d7093, d99068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14091 q ha hb
  have h2 (q : Pattern) (ha : d82212 q = 1) (hb : d98800 q = 1) : d99069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82212, d99069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82212, d99069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6525 q = 1) (hb : d98800 q = 1) : d8014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6525, d8014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14088 q ha hb
    | true =>
      simp only [d6525, d8014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6526 q = 1) (hb : d98800 q = 1) : d8015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6526, d8015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6526, d8015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82213 q = 1) (hb : d98800 q = 1) : d99070 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82213, d99070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82213, d99070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82214 q = 1) (hb : d98800 q = 1) : d99071 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82214, d99071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82214, d99071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82215 q = 1) (hb : d98800 q = 1) : d99072 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82215, d99072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82215, d99072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82216 q = 1) (hb : d98800 q = 1) : d99073 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82216, d99073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82216, d99073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14093 (p : Pattern) (ha : d82222 p = 1) (hb : d98800 p = 1) : d99079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d98800 q = 1) : d7895 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d7895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d7895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14070 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d98800 q = 1) : d7896 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d7896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d7896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d98800 q = 1) : d7904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d7904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14070 q ha hb
    | true =>
      simp only [d1640, d7904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14072 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d98800 q = 1) : d7905 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d7905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d7905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d98800 q = 1) : d7906 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d7906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d7906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82200 q = 1) (hb : d98800 q = 1) : d99048 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82200, d99048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14080 q ha hb
    | true =>
      simp only [d82200, d99048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14086 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d98800 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7068 q = 1) (hb : d98800 q = 1) : d7971 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7068, d7971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14074 q ha hb
    | true =>
      simp only [d7068, d7971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82201 q = 1) (hb : d98800 q = 1) : d99049 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82201, d99049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82201, d99049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82202 q = 1) (hb : d98800 q = 1) : d99050 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82202, d99050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82202, d99050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d82203 q = 1) (hb : d98800 q = 1) : d99051 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82203, d99051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82203, d99051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d82207 q = 1) (hb : d98800 q = 1) : d99055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82207, d99055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82207, d99055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14087 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d98800 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d82208 q = 1) (hb : d98800 q = 1) : d99056 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82208, d99056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82208, d99056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82209 q = 1) (hb : d98800 q = 1) : d99057 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82209, d99057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82209, d99057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82210 q = 1) (hb : d98800 q = 1) : d99058 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82210, d99058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82210, d99058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d82211 q = 1) (hb : d98800 q = 1) : d99059 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82211, d99059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82211, d99059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d82217 q = 1) (hb : d98800 q = 1) : d99074 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82217, d99074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82217, d99074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14092 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d98800 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d82218 q = 1) (hb : d98800 q = 1) : d99075 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82218, d99075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82218, d99075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d82219 q = 1) (hb : d98800 q = 1) : d99076 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82219, d99076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82219, d99076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82220 q = 1) (hb : d98800 q = 1) : d99077 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82220, d99077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82220, d99077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82221 q = 1) (hb : d98800 q = 1) : d99078 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82221, d99078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82221, d99078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d82222 q = 1) (hb : d98800 q = 1) : d99079 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82222, d99079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82222, d99079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro14094 (p : Pattern) (ha : d82228 p = 1) (hb : d98800 p = 1) : d99085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82223 q = 1) (hb : d98800 q = 1) : d99080 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82223, d99080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82223, d99080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14093 q ha hb
  have h2 (q : Pattern) (ha : d82224 q = 1) (hb : d98800 q = 1) : d99081 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82224, d99081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82224, d99081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82225 q = 1) (hb : d98800 q = 1) : d99082 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82225, d99082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82225, d99082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82226 q = 1) (hb : d98800 q = 1) : d99083 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82226, d99083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82226, d99083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82227 q = 1) (hb : d98800 q = 1) : d99084 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82227, d99084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82227, d99084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82228 q = 1) (hb : d98800 q = 1) : d99085 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82228, d99085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82228, d99085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14095 (p : Pattern) (ha : d2102 p = 1) (hb : d98800 p = 1) : d8043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d98800 q = 1) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d98800 q = 1) : d8041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d98800 q = 1) : d8042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d8042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d8042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2102 q = 1) (hb : d98800 q = 1) : d8043 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2102, d8043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2102, d8043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14096 (p : Pattern) (ha : d2112 p = 1) (hb : d98800 p = 1) : d8049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d98800 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2107 q = 1) (hb : d98800 q = 1) : d8044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d8044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14095 q ha hb
    | true =>
      simp only [d2107, d8044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d98800 q = 1) : d8045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d8045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d8045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2109 q = 1) (hb : d98800 q = 1) : d8046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d8046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, d8046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2110 q = 1) (hb : d98800 q = 1) : d8047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d8047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d8047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2111 q = 1) (hb : d98800 q = 1) : d8048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d8048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d8048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2112 q = 1) (hb : d98800 q = 1) : d8049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d8049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d8049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro14097 (p : Pattern) (ha : d2115 p = 1) (hb : d98800 p = 1) : d8052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2099 q = 1) (hb : d98800 q = 1) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d98800 q = 1) : d8041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2100, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d98800 q = 1) : d8042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d8042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d8042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d2115 q = 1) (hb : d98800 q = 1) : d8052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2115, d8052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2115, d8052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14098 (p : Pattern) (ha : d2122 p = 1) (hb : d98800 p = 1) : d8058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d98800 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2107 q = 1) (hb : d98800 q = 1) : d8044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d8044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14095 q ha hb
    | true =>
      simp only [d2107, d8044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d98800 q = 1) : d8045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d8045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d8045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2109 q = 1) (hb : d98800 q = 1) : d8046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d8046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, d8046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2110 q = 1) (hb : d98800 q = 1) : d8047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d8047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d8047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2111 q = 1) (hb : d98800 q = 1) : d8048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d8048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d8048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d98800 q = 1) : d2116 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2117 q = 1) (hb : d98800 q = 1) : d8053 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d8053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14097 q ha hb
    | true =>
      simp only [d2117, d8053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2118 q = 1) (hb : d98800 q = 1) : d8054 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d8054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d8054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2119 q = 1) (hb : d98800 q = 1) : d8055 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d8055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2119, d8055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2120 q = 1) (hb : d98800 q = 1) : d8056 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d8056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d8056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2121 q = 1) (hb : d98800 q = 1) : d8057 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d8057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d8057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2122 q = 1) (hb : d98800 q = 1) : d8058 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d8058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2122, d8058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro14099 (p : Pattern) (ha : d7127 p = 1) (hb : d98800 p = 1) : d8043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5259 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9934 q ha hb
    | true =>
      simp only [d5259, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5260 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5260, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7124 q = 1) (hb : d98800 q = 1) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7124, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7124, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7125 q = 1) (hb : d98800 q = 1) : d8041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7125, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7125, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7126 q = 1) (hb : d98800 q = 1) : d8042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7126, d8042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7126, d8042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7127 q = 1) (hb : d98800 q = 1) : d8043 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7127, d8043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7127, d8043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14100 (p : Pattern) (ha : d7148 p = 1) (hb : d98800 p = 1) : d8125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d98800 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7143 q = 1) (hb : d98800 q = 1) : d8044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7143, d8044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14099 q ha hb
    | true =>
      simp only [d7143, d8044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7144 q = 1) (hb : d98800 q = 1) : d8045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7144, d8045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7144, d8045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7145 q = 1) (hb : d98800 q = 1) : d8046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7145, d8046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7145, d8046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7146 q = 1) (hb : d98800 q = 1) : d8047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7146, d8047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7146, d8047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7147 q = 1) (hb : d98800 q = 1) : d8048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7147, d8048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7147, d8048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d98800 q = 1) : d2309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7148 q = 1) (hb : d98800 q = 1) : d8125 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7148, d8125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7148, d8125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14101 (p : Pattern) (ha : d2127 p = 1) (hb : d98800 p = 1) : d8063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d98800 q = 1) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d98800 q = 1) : d8041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d98800 q = 1) : d8062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d8062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d8062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2127 q = 1) (hb : d98800 q = 1) : d8063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2127, d8063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2127, d8063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14102 (p : Pattern) (ha : d2136 p = 1) (hb : d98800 p = 1) : d8070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d98800 q = 1) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d98800 q = 1) : d8068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d8068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d8068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d98800 q = 1) : d8069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d8069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d8069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2136 q = 1) (hb : d98800 q = 1) : d8070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2136, d8070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2136, d8070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14103 (p : Pattern) (ha : d6550 p = 1) (hb : d98800 p = 1) : d8096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6547 q = 1) (hb : d98800 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d98800, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6547, d98800, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d98800 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d6549 q = 1) (hb : d98800 q = 1) : d8095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6549, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d6550 q = 1) (hb : d98800 q = 1) : d8096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6550, d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6550, d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14104 (p : Pattern) (ha : d7117 p = 1) (hb : d92315 p = 1) : d99091 p = 1 := by
  have h0 (q : Pattern) (ha : d7115 q = 1) (hb : d92313 q = 1) : d7115 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5256 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7116 q = 1) (hb : d92315 q = 1) : d99090 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7116, d92315, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7116, d92315, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7117 q = 1) (hb : d92315 q = 1) : d99091 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7117, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7117, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14105 (p : Pattern) (ha : d7123 p = 1) (hb : d98800 p = 1) : d99097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2156 q = 1) (hb : d77842 q = 1) : d8076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d8076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9939 q ha hb
    | true =>
      simp only [d2156, d8076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2157 q = 1) (hb : d77842 q = 1) : d8077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d8077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2157, d8077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7118 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14104 q ha hb
    | true =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7119 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7120 q = 1) (hb : d98800 q = 1) : d99094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7120, d98800, d99094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7120, d98800, d99094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7121 q = 1) (hb : d98800 q = 1) : d99095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7121, d99095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7121, d99095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7122 q = 1) (hb : d98800 q = 1) : d99096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7122, d99096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7122, d99096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7123 q = 1) (hb : d98800 q = 1) : d99097 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7123, d99097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7123, d99097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro14106 (p : Pattern) (ha : d82237 p = 1) (hb : d98800 p = 1) : d99103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d98800 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2130 q = 1) (hb : d98800 q = 1) : d8064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d8064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14101 q ha hb
    | true =>
      simp only [d2130, d8064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d98800 q = 1) : d8065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d8065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d8065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2132 q = 1) (hb : d98800 q = 1) : d8066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d8066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, d8066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2133 q = 1) (hb : d98800 q = 1) : d8067 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d8067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d8067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d98800 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2140 q = 1) (hb : d98800 q = 1) : d8071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d8071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14102 q ha hb
    | true =>
      simp only [d2140, d8071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2141 q = 1) (hb : d98800 q = 1) : d8072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d8072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d8072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2142 q = 1) (hb : d98800 q = 1) : d8073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d8073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2142, d8073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7128 q = 1) (hb : d98800 q = 1) : d99098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7128, d99098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14105 q ha hb
    | true =>
      simp only [d7128, d99098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14099 q ha hb
  have h11 (q : Pattern) (ha : d82233 q = 1) (hb : d98800 q = 1) : d99099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82233, d99099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82233, d99099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6592 q = 1) (hb : d98800 q = 1) : d8097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d8097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14103 q ha hb
    | true =>
      simp only [d6592, d8097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6593 q = 1) (hb : d98800 q = 1) : d8098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6593, d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82234 q = 1) (hb : d98800 q = 1) : d99100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82234, d99100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82234, d99100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82235 q = 1) (hb : d98800 q = 1) : d99101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82235, d99101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82235, d99101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82236 q = 1) (hb : d98800 q = 1) : d99102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82236, d99102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82236, d99102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d82237 q = 1) (hb : d98800 q = 1) : d99103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82237, d99103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82237, d99103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro14107 (p : Pattern) (ha : d2281 p = 1) (hb : d98800 p = 1) : d8103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d98800 q = 1) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d98800 q = 1) : d8041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d98800 q = 1) : d8062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d8062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d8062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2281 q = 1) (hb : d98800 q = 1) : d8103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2281, d8103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2281, d8103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14108 (p : Pattern) (ha : d2287 p = 1) (hb : d98800 p = 1) : d8108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d98800 q = 1) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2099, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d98800 q = 1) : d8068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d8068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d8068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d98800 q = 1) : d8069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d8069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d8069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2287 q = 1) (hb : d98800 q = 1) : d8108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2287, d8108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2287, d8108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14109 (p : Pattern) (ha : d6559 p = 1) (hb : d98800 p = 1) : d8117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8303 q ha hb
    | true =>
      simp only [d2093, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6547 q = 1) (hb : d98800 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6547, d98800, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6547, d98800, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6548 q = 1) (hb : d98800 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6548, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6549 q = 1) (hb : d98800 q = 1) : d8095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6549, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6549, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6559 q = 1) (hb : d98800 q = 1) : d8117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6559, d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6559, d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14110 (p : Pattern) (ha : d7134 p = 1) (hb : d98800 p = 1) : d99104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d77842 q = 1) : d8076 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d8076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9939 q ha hb
    | true =>
      simp only [d2156, d8076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d77842 q = 1) : d8077 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d8077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d8077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7118 q = 1) (hb : d92315 q = 1) : d99092 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14104 q ha hb
    | true =>
      simp only [d7118, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7119 q = 1) (hb : d92315 q = 1) : d99093 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7119, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7120 q = 1) (hb : d98800 q = 1) : d99094 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7120, d98800, d99094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7120, d98800, d99094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7121 q = 1) (hb : d98800 q = 1) : d99095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7121, d99095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7121, d99095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7122 q = 1) (hb : d98800 q = 1) : d99096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7122, d99096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7122, d99096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d7134 q = 1) (hb : d98800 q = 1) : d99104 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7134, d99104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7134, d99104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14111 (p : Pattern) (ha : d7135 p = 1) (hb : d98800 p = 1) : d8052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5259 q = 1) (hb : d77842 q = 1) : d8038 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5259, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9934 q ha hb
    | true =>
      simp only [d5259, d8038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5260 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5260, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5260, d8039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d92315 q = 1) : d2098 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7124 q = 1) (hb : d98800 q = 1) : d8040 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7124, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7124, d98800, d8040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7125 q = 1) (hb : d98800 q = 1) : d8041 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7125, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7125, d8041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7126 q = 1) (hb : d98800 q = 1) : d8042 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7126, d8042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7126, d8042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d7135 q = 1) (hb : d98800 q = 1) : d8052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7135, d8052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7135, d8052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14112 (p : Pattern) (ha : d82242 p = 1) (hb : d98800 p = 1) : d99110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d98800 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2130 q = 1) (hb : d98800 q = 1) : d8064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d8064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14101 q ha hb
    | true =>
      simp only [d2130, d8064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d98800 q = 1) : d8065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d8065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d8065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2132 q = 1) (hb : d98800 q = 1) : d8066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d8066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, d8066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2133 q = 1) (hb : d98800 q = 1) : d8067 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d8067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d8067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d98800 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2140 q = 1) (hb : d98800 q = 1) : d8071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d8071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14102 q ha hb
    | true =>
      simp only [d2140, d8071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2141 q = 1) (hb : d98800 q = 1) : d8072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d8072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d8072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2142 q = 1) (hb : d98800 q = 1) : d8073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d8073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2142, d8073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7128 q = 1) (hb : d98800 q = 1) : d99098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7128, d99098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14105 q ha hb
    | true =>
      simp only [d7128, d99098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14099 q ha hb
  have h11 (q : Pattern) (ha : d82233 q = 1) (hb : d98800 q = 1) : d99099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82233, d99099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82233, d99099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d6592 q = 1) (hb : d98800 q = 1) : d8097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6592, d8097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14103 q ha hb
    | true =>
      simp only [d6592, d8097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d6593 q = 1) (hb : d98800 q = 1) : d8098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6593, d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d6593, d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d82234 q = 1) (hb : d98800 q = 1) : d99100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82234, d99100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82234, d99100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82235 q = 1) (hb : d98800 q = 1) : d99101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82235, d99101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82235, d99101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82236 q = 1) (hb : d98800 q = 1) : d99102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82236, d99102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82236, d99102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2282 q = 1) (hb : d98800 q = 1) : d2282 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d2283 q = 1) (hb : d98800 q = 1) : d8104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d8104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14107 q ha hb
    | true =>
      simp only [d2283, d8104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2284 q = 1) (hb : d98800 q = 1) : d8105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d8105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2284, d8105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d2285 q = 1) (hb : d98800 q = 1) : d8106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d8106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d2285, d8106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d2286 q = 1) (hb : d98800 q = 1) : d8107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d8107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d8107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d2288 q = 1) (hb : d98800 q = 1) : d2288 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d2289 q = 1) (hb : d98800 q = 1) : d8109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d8109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14108 q ha hb
    | true =>
      simp only [d2289, d8109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d2290 q = 1) (hb : d98800 q = 1) : d8110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d8110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d8110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d2291 q = 1) (hb : d98800 q = 1) : d8111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d8111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d2291, d8111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d7136 q = 1) (hb : d98800 q = 1) : d99105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7136, d99105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14110 q ha hb
    | true =>
      simp only [d7136, d99105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14111 q ha hb
  have h27 (q : Pattern) (ha : d82238 q = 1) (hb : d98800 q = 1) : d99106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82238, d99106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d82238, d99106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d6613 q = 1) (hb : d98800 q = 1) : d8118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d8118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14109 q ha hb
    | true =>
      simp only [d6613, d8118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d6614 q = 1) (hb : d98800 q = 1) : d8119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d6614, d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d82239 q = 1) (hb : d98800 q = 1) : d99107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82239, d99107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d82239, d99107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d82240 q = 1) (hb : d98800 q = 1) : d99108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82240, d99108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d82240, d99108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d82241 q = 1) (hb : d98800 q = 1) : d99109 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82241, d99109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82241, d99109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d82242 q = 1) (hb : d98800 q = 1) : d99110 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82242, d99110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d82242, d99110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro14113 (p : Pattern) (ha : d82249 p = 1) (hb : d98800 p = 1) : d99117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7136 q = 1) (hb : d98800 q = 1) : d99105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7136, d99105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14110 q ha hb
    | true =>
      simp only [d7136, d99105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14111 q ha hb
  have h2 (q : Pattern) (ha : d82238 q = 1) (hb : d98800 q = 1) : d99106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82238, d99106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82238, d99106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6613 q = 1) (hb : d98800 q = 1) : d8118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6613, d8118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14109 q ha hb
    | true =>
      simp only [d6613, d8118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6614 q = 1) (hb : d98800 q = 1) : d8119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6614, d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6614, d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82239 q = 1) (hb : d98800 q = 1) : d99107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82239, d99107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82239, d99107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82247 q = 1) (hb : d98800 q = 1) : d99115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82247, d99115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82247, d99115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82248 q = 1) (hb : d98800 q = 1) : d99116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82248, d99116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82248, d99116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82249 q = 1) (hb : d98800 q = 1) : d99117 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82249, d99117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82249, d99117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14114 (p : Pattern) (ha : d6671 p = 1) (hb : d98800 p = 1) : d8168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d77842 q = 1) : d8144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8311 q ha hb
    | true =>
      simp only [d2378, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d77842 q = 1) : d8145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6668 q = 1) (hb : d98800 q = 1) : d8165 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d6668, d98800, d8165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6668, d98800, d8165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d6669 q = 1) (hb : d98800 q = 1) : d8166 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d6669, d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d6669, d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6670 q = 1) (hb : d98800 q = 1) : d8167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d6670, d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6670, d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d6671 q = 1) (hb : d98800 q = 1) : d8168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d6671, d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6671, d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14115 (p : Pattern) (ha : d7163 p = 1) (hb : d92315 p = 1) : d99124 p = 1 := by
  have h0 (q : Pattern) (ha : d7161 q = 1) (hb : d92313 q = 1) : d7161 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6652 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7162 q = 1) (hb : d92315 q = 1) : d99123 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d7162, d92315, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7162, d92315, d99123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7163 q = 1) (hb : d92315 q = 1) : d99124 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d7163, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7163, d99124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro14116 (p : Pattern) (ha : d7169 p = 1) (hb : d98800 p = 1) : d99130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d77842 q = 1) : d8140 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d8140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9948 q ha hb
    | true =>
      simp only [d2373, d8140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d77842 q = 1) : d8141 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d8141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d8141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7164 q = 1) (hb : d92315 q = 1) : d99125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7164, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14115 q ha hb
    | true =>
      simp only [d7164, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7165 q = 1) (hb : d92315 q = 1) : d99126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7165, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7165, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7166 q = 1) (hb : d98800 q = 1) : d99127 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7166, d98800, d99127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7166, d98800, d99127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7167 q = 1) (hb : d98800 q = 1) : d99128 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7167, d99128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7167, d99128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7168 q = 1) (hb : d98800 q = 1) : d99129 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7168, d99129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7168, d99129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d7169 q = 1) (hb : d98800 q = 1) : d99130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7169, d99130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7169, d99130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro14117 (p : Pattern) (ha : d7173 p = 1) (hb : d98800 p = 1) : d8153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6655 q = 1) (hb : d77842 q = 1) : d8144 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6655, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9950 q ha hb
    | true =>
      simp only [d6655, d8144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6656 q = 1) (hb : d77842 q = 1) : d8145 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6656, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6656, d8145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2387 q = 1) (hb : d92315 q = 1) : d2387 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7170 q = 1) (hb : d98800 q = 1) : d8150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7170, d98800, d8150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7170, d98800, d8150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d7171 q = 1) (hb : d98800 q = 1) : d8151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7171, d8151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7171, d8151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7172 q = 1) (hb : d98800 q = 1) : d8152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7172, d8152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7172, d8152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d7173 q = 1) (hb : d98800 q = 1) : d8153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7173, d8153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7173, d8153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14118 (p : Pattern) (ha : d82259 p = 1) (hb : d98800 p = 1) : d99136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7174 q = 1) (hb : d98800 q = 1) : d99131 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7174, d99131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14116 q ha hb
    | true =>
      simp only [d7174, d99131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14117 q ha hb
  have h2 (q : Pattern) (ha : d82255 q = 1) (hb : d98800 q = 1) : d99132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d82255, d99132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82255, d99132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d6672 q = 1) (hb : d98800 q = 1) : d8169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d6672, d8169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14114 q ha hb
    | true =>
      simp only [d6672, d8169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6673 q = 1) (hb : d98800 q = 1) : d8170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d6673, d8170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6673, d8170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82256 q = 1) (hb : d98800 q = 1) : d99133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d82256, d99133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82256, d99133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82257 q = 1) (hb : d98800 q = 1) : d99134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d82257, d99134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82257, d99134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82258 q = 1) (hb : d98800 q = 1) : d99135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d82258, d99135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82258, d99135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d82259 q = 1) (hb : d98800 q = 1) : d99136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d82259, d99136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82259, d99136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14119 (p : Pattern) (ha : d82265 p = 1) (hb : d98800 p = 1) : d99142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d98800 q = 1) : d8050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d8050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d8050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14096 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d98800 q = 1) : d8051 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d8051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d8051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d98800 q = 1) : d8059 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d8059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14096 q ha hb
    | true =>
      simp only [d2123, d8059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14098 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d98800 q = 1) : d8060 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d8060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d8060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d98800 q = 1) : d8061 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d8061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d8061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82243 q = 1) (hb : d98800 q = 1) : d99111 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82243, d99111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14106 q ha hb
    | true =>
      simp only [d82243, d99111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14112 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d98800 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7149 q = 1) (hb : d98800 q = 1) : d8126 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7149, d8126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14100 q ha hb
    | true =>
      simp only [d7149, d8126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82244 q = 1) (hb : d98800 q = 1) : d99112 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82244, d99112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82244, d99112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82245 q = 1) (hb : d98800 q = 1) : d99113 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82245, d99113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d82245, d99113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d82246 q = 1) (hb : d98800 q = 1) : d99114 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82246, d99114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82246, d99114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d82250 q = 1) (hb : d98800 q = 1) : d99118 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82250, d99118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82250, d99118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14113 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d98800 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d82251 q = 1) (hb : d98800 q = 1) : d99119 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82251, d99119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d82251, d99119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82252 q = 1) (hb : d98800 q = 1) : d99120 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82252, d99120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d82252, d99120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d82253 q = 1) (hb : d98800 q = 1) : d99121 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82253, d99121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82253, d99121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d82254 q = 1) (hb : d98800 q = 1) : d99122 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82254, d99122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d82254, d99122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d82260 q = 1) (hb : d98800 q = 1) : d99137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d82260, d99137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82260, d99137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14118 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d98800 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d82261 q = 1) (hb : d98800 q = 1) : d99138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d82261, d99138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d82261, d99138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d82262 q = 1) (hb : d98800 q = 1) : d99139 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d82262, d99139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d82262, d99139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d82263 q = 1) (hb : d98800 q = 1) : d99140 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d82263, d99140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d82263, d99140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d82264 q = 1) (hb : d98800 q = 1) : d99141 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d82264, d99141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d82264, d99141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d82265 q = 1) (hb : d98800 q = 1) : d99142 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d82265, d99142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d82265, d99142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro14120 (p : Pattern) (ha : d82271 p = 1) (hb : d98800 p = 1) : d99148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82266 q = 1) (hb : d98800 q = 1) : d99143 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d82266, d99143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82266, d99143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14119 q ha hb
  have h2 (q : Pattern) (ha : d82267 q = 1) (hb : d98800 q = 1) : d99144 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d82267, d99144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82267, d99144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d82268 q = 1) (hb : d98800 q = 1) : d99145 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d82268, d99145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82268, d99145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82269 q = 1) (hb : d98800 q = 1) : d99146 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d82269, d99146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82269, d99146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d82270 q = 1) (hb : d98800 q = 1) : d99147 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d82270, d99147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82270, d99147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82271 q = 1) (hb : d98800 q = 1) : d99148 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d82271, d99148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82271, d99148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14121 (p : Pattern) (ha : d82277 p = 1) (hb : d98800 p = 1) : d99154 p = 1 := by
  have h0 (q : Pattern) (ha : d82106 q = 1) (hb : d98800 q = 1) : d98903 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82106, d98903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro13990 q ha hb
    | true =>
      simp only [d82106, d98903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14016 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d82146 q = 1) (hb : d98800 q = 1) : d98963 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82146, d98963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82146, d98963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14042 q ha hb
  have h3 (q : Pattern) (ha : d82147 q = 1) (hb : d98800 q = 1) : d98964 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82147, d98964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d82147, d98964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d82187 q = 1) (hb : d98800 q = 1) : d99024 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82187, d99024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82187, d99024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14068 q ha hb
  have h5 (q : Pattern) (ha : d82188 q = 1) (hb : d98800 q = 1) : d99025 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82188, d99025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82188, d99025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d82189 q = 1) (hb : d98800 q = 1) : d99026 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82189, d99026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82189, d99026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82229 q = 1) (hb : d98800 q = 1) : d99086 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82229, d99086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82229, d99086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14094 q ha hb
  have h8 (q : Pattern) (ha : d82230 q = 1) (hb : d98800 q = 1) : d99087 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82230, d99087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82230, d99087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d82231 q = 1) (hb : d98800 q = 1) : d99088 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82231, d99088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82231, d99088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d82232 q = 1) (hb : d98800 q = 1) : d99089 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82232, d99089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82232, d99089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d82272 q = 1) (hb : d98800 q = 1) : d99149 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d82272, d99149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82272, d99149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14120 q ha hb
  have h12 (q : Pattern) (ha : d82273 q = 1) (hb : d98800 q = 1) : d99150 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d82273, d99150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82273, d99150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d82274 q = 1) (hb : d98800 q = 1) : d99151 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d82274, d99151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82274, d99151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d82275 q = 1) (hb : d98800 q = 1) : d99152 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d82275, d99152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82275, d99152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d82276 q = 1) (hb : d98800 q = 1) : d99153 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d82276, d99153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d82276, d99153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d82277 q = 1) (hb : d98800 q = 1) : d99154 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d82277, d99154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d82277, d99154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro14122 (p : Pattern) (ha : d82283 p = 1) (hb : d98800 p = 1) : d99160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82278 q = 1) (hb : d98800 q = 1) : d99155 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d82278, d99155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14121 q ha hb
    | true =>
      simp only [d82278, d99155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82279 q = 1) (hb : d98800 q = 1) : d99156 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d82279, d99156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82279, d99156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82280 q = 1) (hb : d98800 q = 1) : d99157 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d82280, d99157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82280, d99157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82281 q = 1) (hb : d98800 q = 1) : d99158 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d82281, d99158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82281, d99158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82282 q = 1) (hb : d98800 q = 1) : d99159 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d82282, d99159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82282, d99159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82283 q = 1) (hb : d98800 q = 1) : d99160 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d82283, d99160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82283, d99160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14123 (p : Pattern) (ha : d82289 p = 1) (hb : d98800 p = 1) : d99166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82284 q = 1) (hb : d98800 q = 1) : d99161 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d82284, d99161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14122 q ha hb
    | true =>
      simp only [d82284, d99161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82285 q = 1) (hb : d98800 q = 1) : d99162 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d82285, d99162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82285, d99162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82286 q = 1) (hb : d98800 q = 1) : d99163 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d82286, d99163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82286, d99163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82287 q = 1) (hb : d98800 q = 1) : d99164 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d82287, d99164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82287, d99164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82288 q = 1) (hb : d98800 q = 1) : d99165 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d82288, d99165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82288, d99165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82289 q = 1) (hb : d98800 q = 1) : d99166 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d82289, d99166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82289, d99166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14124 (p : Pattern) (ha : d82295 p = 1) (hb : d98800 p = 1) : d99172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82290 q = 1) (hb : d98800 q = 1) : d99167 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d82290, d99167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14123 q ha hb
    | true =>
      simp only [d82290, d99167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82291 q = 1) (hb : d98800 q = 1) : d99168 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d82291, d99168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82291, d99168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82292 q = 1) (hb : d98800 q = 1) : d99169 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d82292, d99169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82292, d99169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82293 q = 1) (hb : d98800 q = 1) : d99170 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d82293, d99170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82293, d99170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82294 q = 1) (hb : d98800 q = 1) : d99171 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d82294, d99171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82294, d99171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82295 q = 1) (hb : d98800 q = 1) : d99172 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d82295, d99172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82295, d99172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14125 (p : Pattern) (ha : d82301 p = 1) (hb : d98800 p = 1) : d99178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82296 q = 1) (hb : d98800 q = 1) : d99173 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d82296, d99173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14124 q ha hb
    | true =>
      simp only [d82296, d99173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82297 q = 1) (hb : d98800 q = 1) : d99174 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d82297, d99174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82297, d99174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82298 q = 1) (hb : d98800 q = 1) : d99175 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d82298, d99175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82298, d99175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82299 q = 1) (hb : d98800 q = 1) : d99176 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d82299, d99176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82299, d99176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82300 q = 1) (hb : d98800 q = 1) : d99177 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d82300, d99177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82300, d99177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82301 q = 1) (hb : d98800 q = 1) : d99178 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d82301, d99178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82301, d99178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14126 (p : Pattern) (ha : d82307 p = 1) (hb : d98801 p = 1) : d99184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82302 q = 1) (hb : d98800 q = 1) : d99179 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d82302, d99179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14125 q ha hb
    | true =>
      simp only [d82302, d99179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82303 q = 1) (hb : d98800 q = 1) : d99180 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d82303, d99180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82303, d99180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d82304 q = 1) (hb : d98801 q = 1) : d99181 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d82304, d98801, d99181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82304, d98801, d99181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d98801 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d82305 q = 1) (hb : d98801 q = 1) : d99182 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d82305, d99182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82305, d99182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d82306 q = 1) (hb : d98801 q = 1) : d99183 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d82306, d99183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d82306, d99183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d82307 q = 1) (hb : d98801 q = 1) : d99184 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d82307, d99184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d82307, d99184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro14127 (p : Pattern) (ha : d82313 p = 1) (hb : d98801 p = 1) : d99190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98801 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82308 q = 1) (hb : d98801 q = 1) : d99185 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d82308, d99185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14126 q ha hb
    | true =>
      simp only [d82308, d99185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82309 q = 1) (hb : d98801 q = 1) : d99186 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d82309, d99186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82309, d99186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82310 q = 1) (hb : d98801 q = 1) : d99187 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d82310, d99187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82310, d99187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82311 q = 1) (hb : d98801 q = 1) : d99188 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d82311, d99188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82311, d99188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82312 q = 1) (hb : d98801 q = 1) : d99189 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d82312, d99189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82312, d99189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82313 q = 1) (hb : d98801 q = 1) : d99190 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d82313, d99190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82313, d99190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14128 (p : Pattern) (ha : d82319 p = 1) (hb : d98801 p = 1) : d99196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d98801 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d82314 q = 1) (hb : d98801 q = 1) : d99191 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d82314, d99191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14127 q ha hb
    | true =>
      simp only [d82314, d99191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d82315 q = 1) (hb : d98801 q = 1) : d99192 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d82315, d99192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d82315, d99192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d82316 q = 1) (hb : d98801 q = 1) : d99193 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d82316, d99193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d82316, d99193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d82317 q = 1) (hb : d98801 q = 1) : d99194 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d82317, d99194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d82317, d99194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d82318 q = 1) (hb : d98801 q = 1) : d99195 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d82318, d99195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d82318, d99195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d82319 q = 1) (hb : d98801 q = 1) : d99196 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d82319, d99196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d82319, d99196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro14129 (p : Pattern) (ha : d7247 p = 1) (hb : d83670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7245 q = 1) (hb : d83668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7246 q = 1) (hb : d83669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d83669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7246, d83669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7247 q = 1) (hb : d83670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, d83670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7247, d83670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14130 (p : Pattern) (ha : d83676 p = 1) (hb : d85394 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7248 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q ha hb
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d85390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d83672, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d85391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d85392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d85393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83676 q = 1) (hb : d85394 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83676, d85394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83676, d85394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro14131 (p : Pattern) (ha : d7254 p = 1) (hb : d83677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7245 q = 1) (hb : d83668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7246 q = 1) (hb : d83669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d83669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7246, d83669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7254 q = 1) (hb : d83677 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, d83677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7254, d83677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14132 (p : Pattern) (ha : d83683 p = 1) (hb : d85399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d51969 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d51970 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d51971 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7248 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q ha hb
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83672 q = 1) (hb : d85390 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83672, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d83672, d85390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83673 q = 1) (hb : d85391 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83673, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83673, d85391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83674 q = 1) (hb : d85392 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83674, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83674, d85392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83675 q = 1) (hb : d85393 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83675, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83675, d85393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d195 q = 1) (hb : d52015 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d196 q = 1) (hb : d52016 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d197 q = 1) (hb : d52017 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d198 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7255 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14131 q ha hb
    | true =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83679 q = 1) (hb : d85395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d83679, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d83680 q = 1) (hb : d85396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83680, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83681 q = 1) (hb : d85397 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83681, d85397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d83681, d85397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83682 q = 1) (hb : d85398 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83682, d85398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d83682, d85398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83683 q = 1) (hb : d85399 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83683, d85399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83683, d85399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro14133 (p : Pattern) (ha : d83690 p = 1) (hb : d85406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7255 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14131 q ha hb
    | true =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83679 q = 1) (hb : d85395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83679, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83679, d85395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d50 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83680 q = 1) (hb : d85396 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83680, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83680, d85396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83688 q = 1) (hb : d85404 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83688, d85404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83688, d85404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83689 q = 1) (hb : d85405 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83689, d85405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83689, d85405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83690 q = 1) (hb : d85406 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83690, d85406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83690, d85406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14134 (p : Pattern) (ha : d7280 p = 1) (hb : d83703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7275 q = 1) (hb : d83698 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9970 q ha hb
    | true =>
      simp only [d7275, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7276 q = 1) (hb : d83699 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7276, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7277 q = 1) (hb : d83700 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, d83700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7277, d83700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7278 q = 1) (hb : d83701 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, d83701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7278, d83701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7279 q = 1) (hb : d83702 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, d83702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7279, d83702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7280 q = 1) (hb : d83703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, d83703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7280, d83703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14135 (p : Pattern) (ha : d83709 p = 1) (hb : d85416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7281 q = 1) (hb : d83704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d83704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14134 q ha hb
    | true =>
      simp only [d7281, d83704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83705 q = 1) (hb : d85412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83705, d85412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83705, d85412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83706 q = 1) (hb : d85413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83706, d85413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83706, d85413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83707 q = 1) (hb : d85414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83707, d85414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83707, d85414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83708 q = 1) (hb : d85415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83708, d85415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83708, d85415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83709 q = 1) (hb : d85416 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83709, d85416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83709, d85416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14136 (p : Pattern) (ha : d83715 p = 1) (hb : d85422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d51957 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d51958 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d51964 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15 q ha hb
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d51965 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83684 q = 1) (hb : d85400 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83684, d85400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14130 q ha hb
    | true =>
      simp only [d83684, d85400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14132 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro17 q ha hb
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83685 q = 1) (hb : d85401 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83685, d85401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83685, d85401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d83686 q = 1) (hb : d85402 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83686, d85402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83686, d85402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83687 q = 1) (hb : d85403 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83687, d85403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83687, d85403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83691 q = 1) (hb : d85407 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83691, d85407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83691, d85407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14133 q ha hb
  have h12 (q : Pattern) (ha : d83692 q = 1) (hb : d85408 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83692, d85408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83692, d85408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83693 q = 1) (hb : d85409 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83693, d85409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83693, d85409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83694 q = 1) (hb : d85410 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83694, d85410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83694, d85410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83695 q = 1) (hb : d85411 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83695, d85411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83695, d85411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83710 q = 1) (hb : d85417 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83710, d85417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83710, d85417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14135 q ha hb
  have h17 (q : Pattern) (ha : d83711 q = 1) (hb : d85418 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83711, d85418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83711, d85418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d83712 q = 1) (hb : d85419 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83712, d85419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83712, d85419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d83713 q = 1) (hb : d85420 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83713, d85420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d83713, d85420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d83714 q = 1) (hb : d85421 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83714, d85421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83714, d85421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83715 q = 1) (hb : d85422 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83715, d85422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83715, d85422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro14137 (p : Pattern) (ha : d7302 p = 1) (hb : d83725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7248 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q ha hb
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d7298 q = 1) (hb : d83721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7299 q = 1) (hb : d83722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7300 q = 1) (hb : d83723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7301 q = 1) (hb : d83724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7302 q = 1) (hb : d83725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d83725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d83725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14138 (p : Pattern) (ha : d7309 p = 1) (hb : d83732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7248 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q ha hb
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d7298 q = 1) (hb : d83721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7299 q = 1) (hb : d83722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7300 q = 1) (hb : d83723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7301 q = 1) (hb : d83724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7255 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14131 q ha hb
    | true =>
      simp only [d7255, d83678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d7305 q = 1) (hb : d83728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d83728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d83728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7306 q = 1) (hb : d83729 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d83729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7306, d83729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7307 q = 1) (hb : d83730 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d83730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d83730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7308 q = 1) (hb : d83731 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d83731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d83731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7309 q = 1) (hb : d83732 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d83732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7309, d83732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14139 (p : Pattern) (ha : d7376 p = 1) (hb : d83788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7248 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q ha hb
    | true =>
      simp only [d7248, d83671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d7298 q = 1) (hb : d83721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d83721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7299 q = 1) (hb : d83722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7299, d83722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7300 q = 1) (hb : d83723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d83723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7301 q = 1) (hb : d83724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d83724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7376 q = 1) (hb : d83788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, d83788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7376, d83788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14140 (p : Pattern) (ha : d7314 p = 1) (hb : d83737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7245 q = 1) (hb : d83668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7313 q = 1) (hb : d83736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d83736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d83736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7314 q = 1) (hb : d83737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, d83737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7314, d83737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14141 (p : Pattern) (ha : d7321 p = 1) (hb : d83744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7319 q = 1) (hb : d83742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d83742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d83742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7320 q = 1) (hb : d83743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d83743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7320, d83743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7321 q = 1) (hb : d83744 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, d83744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7321, d83744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14142 (p : Pattern) (ha : d481 p = 1) (hb : d83664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d145, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d51999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d51999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d83663 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d83663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d83663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d83664 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d83664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d83664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14143 (p : Pattern) (ha : d7433 p = 1) (hb : d83755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d83752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d83752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d83753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d83753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d83754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d83754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d83754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7433 q = 1) (hb : d83755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d83755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7433, d83755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14144 (p : Pattern) (ha : d83767 p = 1) (hb : d98807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7315 q = 1) (hb : d83738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d83738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14140 q ha hb
    | true =>
      simp only [d7315, d83738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d7316 q = 1) (hb : d83739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d83739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d83739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7317 q = 1) (hb : d83740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d83740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7317, d83740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7318 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d83741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d83741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7322 q = 1) (hb : d83745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d83745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14141 q ha hb
    | true =>
      simp only [d7322, d83745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d7323 q = 1) (hb : d83746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d83746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d83746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7324 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d83747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7324, d83747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d98802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d98802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14143 q hb ha
    | true =>
      simp only [d83756, d98802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d98803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d98803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d98803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7348 q = 1) (hb : d83762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9976 q ha hb
    | true =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d98804 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d98804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d98804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d98805 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d98805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83765, d98805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d98806 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d98806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83766, d98806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83767 q = 1) (hb : d98807 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83767, d98807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83767, d98807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro14145 (p : Pattern) (ha : d7354 p = 1) (hb : d83768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7245 q = 1) (hb : d83668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7245, d83668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7313 q = 1) (hb : d83736 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d83736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d83736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7354 q = 1) (hb : d83768 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, d83768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7354, d83768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14146 (p : Pattern) (ha : d7359 p = 1) (hb : d83773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7242 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9964 q ha hb
    | true =>
      simp only [d7242, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7244 q = 1) (hb : d83667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7244, d83667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7319 q = 1) (hb : d83742 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d83742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d83742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7320 q = 1) (hb : d83743 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d83743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7320, d83743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7359 q = 1) (hb : d83773 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, d83773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7359, d83773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14147 (p : Pattern) (ha : d7442 p = 1) (hb : d83777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d83665 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14142 q ha hb
    | true =>
      simp only [d482, d83665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d83666 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d83666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d83752 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d83752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d83753 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d83753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d83754 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d83754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d83754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7442 q = 1) (hb : d83777 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d83777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7442, d83777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14148 (p : Pattern) (ha : d83786 p = 1) (hb : d98813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7315 q = 1) (hb : d83738 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d83738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14140 q ha hb
    | true =>
      simp only [d7315, d83738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d7316 q = 1) (hb : d83739 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d83739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d83739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7317 q = 1) (hb : d83740 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d83740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7317, d83740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7318 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d83741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d83741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7322 q = 1) (hb : d83745 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d83745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14141 q ha hb
    | true =>
      simp only [d7322, d83745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d7323 q = 1) (hb : d83746 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d83746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d83746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7324 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d83747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7324, d83747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83756 q = 1) (hb : d98802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83756, d98802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14143 q hb ha
    | true =>
      simp only [d83756, d98802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14129 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83671 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83757 q = 1) (hb : d98803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d98803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83757, d98803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7348 q = 1) (hb : d83762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9976 q ha hb
    | true =>
      simp only [d7348, d83762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7349, d83763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83764 q = 1) (hb : d98804 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d98804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83764, d98804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83765 q = 1) (hb : d98805 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d98805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83765, d98805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83766 q = 1) (hb : d98806 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d98806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83766, d98806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7355 q = 1) (hb : d83769 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, d83769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14145 q ha hb
    | true =>
      simp only [d7355, d83769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d7356 q = 1) (hb : d83770 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, d83770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7356, d83770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7357 q = 1) (hb : d83771 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, d83771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7357, d83771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7358 q = 1) (hb : d83772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, d83772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7358, d83772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7360 q = 1) (hb : d83774 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, d83774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14146 q ha hb
    | true =>
      simp only [d7360, d83774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d7361 q = 1) (hb : d83775 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, d83775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7361, d83775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7362 q = 1) (hb : d83776 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, d83776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7362, d83776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d83778 q = 1) (hb : d98808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d98808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14147 q hb ha
    | true =>
      simp only [d83778, d98808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14131 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83779 q = 1) (hb : d98809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d98809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83779, d98809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7369 q = 1) (hb : d83781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9982 q ha hb
    | true =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7370 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d83783 q = 1) (hb : d98810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d98810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83783, d98810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83784 q = 1) (hb : d98811 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83784, d98811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d83784, d98811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83785 q = 1) (hb : d98812 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83785, d98812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d83785, d98812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83786 q = 1) (hb : d98813 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83786, d98813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83786, d98813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro14149 (p : Pattern) (ha : d83795 p = 1) (hb : d98820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83778 q = 1) (hb : d98808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83778, d98808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14147 q hb ha
    | true =>
      simp only [d83778, d98808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14131 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83678 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83779 q = 1) (hb : d98809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d98809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83779, d98809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7369 q = 1) (hb : d83781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9982 q ha hb
    | true =>
      simp only [d7369, d83781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7370 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7370, d83782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83783 q = 1) (hb : d98810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d98810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83783, d98810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83793 q = 1) (hb : d98818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83793, d98818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83793, d98818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83794 q = 1) (hb : d98819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83794, d98819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83794, d98819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83795 q = 1) (hb : d98820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d98820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d98820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14150 (p : Pattern) (ha : d683 p = 1) (hb : d83697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d232 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d233 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d234 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d52053 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d673, d52053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d83696 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d83696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d83696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d83697 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d83697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d83697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro14151 (p : Pattern) (ha : d7539 p = 1) (hb : d83808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d83803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9990 q ha hb
    | true =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d83804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d83698 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14150 q ha hb
    | true =>
      simp only [d684, d83698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d83699 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d83699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7536 q = 1) (hb : d83805 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d83805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7536, d83805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7537 q = 1) (hb : d83806 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d83806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7537, d83806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7538 q = 1) (hb : d83807 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d83807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7538, d83807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7539 q = 1) (hb : d83808 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d83808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7539, d83808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14152 (p : Pattern) (ha : d83820 p = 1) (hb : d98831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83809 q = 1) (hb : d98826 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83809, d98826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14151 q hb ha
    | true =>
      simp only [d83809, d98826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14134 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d98827 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d98827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83810, d98827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7412 q = 1) (hb : d83815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d83815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9989 q ha hb
    | true =>
      simp only [d7412, d83815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7413 q = 1) (hb : d83816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, d83816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7413, d83816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83817 q = 1) (hb : d98828 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d98828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d98828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83818 q = 1) (hb : d98829 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d98829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d98829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83819 q = 1) (hb : d98830 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d98830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d98830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83820 q = 1) (hb : d98831 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d98831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d98831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14153 (p : Pattern) (ha : d83826 p = 1) (hb : d98837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7303 q = 1) (hb : d83726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, d83726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7303, d83726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14137 q ha hb
  have h2 (q : Pattern) (ha : d7304 q = 1) (hb : d83727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, d83727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7304, d83727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7310 q = 1) (hb : d83733 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d83733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14137 q ha hb
    | true =>
      simp only [d7310, d83733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14138 q ha hb
  have h4 (q : Pattern) (ha : d7311 q = 1) (hb : d83734 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d83734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7311, d83734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7312 q = 1) (hb : d83735 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, d83735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7312, d83735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83787 q = 1) (hb : d98814 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83787, d98814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14144 q ha hb
    | true =>
      simp only [d83787, d98814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14148 q ha hb
  have h7 (q : Pattern) (ha : d7377 q = 1) (hb : d83789 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, d83789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14139 q ha hb
    | true =>
      simp only [d7377, d83789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d83790 q = 1) (hb : d98815 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83790, d98815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83790, d98815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d83791 q = 1) (hb : d98816 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d98816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83791, d98816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83792 q = 1) (hb : d98817 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d98817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83792, d98817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83796 q = 1) (hb : d98821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d98821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83796, d98821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14149 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d83797 q = 1) (hb : d98822 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d98822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83797, d98822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83798 q = 1) (hb : d98823 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d98823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83798, d98823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83799 q = 1) (hb : d98824 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d98824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83799, d98824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83800 q = 1) (hb : d98825 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d98825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83800, d98825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83821 q = 1) (hb : d98832 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d98832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83821, d98832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14152 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d83822 q = 1) (hb : d98833 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d98833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83822, d98833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83823 q = 1) (hb : d98834 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d98834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83823, d98834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83824 q = 1) (hb : d98835 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d98835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83824, d98835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83825 q = 1) (hb : d98836 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d98836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83825, d98836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83826 q = 1) (hb : d98837 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d98837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83826, d98837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro14154 (p : Pattern) (ha : d83832 p = 1) (hb : d98843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83716 q = 1) (hb : d85423 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83716, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83716, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14136 q ha hb
  have h6 (q : Pattern) (ha : d83717 q = 1) (hb : d85424 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83717, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83717, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83718 q = 1) (hb : d85425 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83718, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83718, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83719 q = 1) (hb : d85426 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83719, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83719, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83720 q = 1) (hb : d85427 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83720, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83720, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83827 q = 1) (hb : d98838 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d98838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83827, d98838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14153 q ha hb
  have h11 (q : Pattern) (ha : d83828 q = 1) (hb : d98839 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d98839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83828, d98839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83829 q = 1) (hb : d98840 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d98840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83829, d98840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83830 q = 1) (hb : d98841 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d98841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83830, d98841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83831 q = 1) (hb : d98842 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d98842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83831, d98842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83832 q = 1) (hb : d98843 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d98843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83832, d98843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro14155 (p : Pattern) (ha : d7433 p = 1) (hb : d83836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d83833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d83834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d83835 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d83835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d83835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7433 q = 1) (hb : d83836 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d83836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7433, d83836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14156 (p : Pattern) (ha : d7439 p = 1) (hb : d83842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14155 q ha hb
    | true =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d83838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d83839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d83840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d83841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7439 q = 1) (hb : d83842 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d83842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d83842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14157 (p : Pattern) (ha : d7442 p = 1) (hb : d83845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d83833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d83834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7432 q = 1) (hb : d83835 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d83835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7432, d83835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7442 q = 1) (hb : d83845 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d83845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7442, d83845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14158 (p : Pattern) (ha : d7448 p = 1) (hb : d83851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14155 q ha hb
    | true =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d83838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d83839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d83840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d83841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7443 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d83846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14157 q ha hb
    | true =>
      simp only [d7443, d83846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q ha hb
  have h7 (q : Pattern) (ha : d7444 q = 1) (hb : d83847 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d83847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d83847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7445 q = 1) (hb : d83848 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d83848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7445, d83848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7446 q = 1) (hb : d83849 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d83849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d83849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7447 q = 1) (hb : d83850 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d83850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d83850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7448 q = 1) (hb : d83851 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d83851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7448, d83851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14159 (p : Pattern) (ha : d7515 p = 1) (hb : d83907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7434 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14155 q ha hb
    | true =>
      simp only [d7434, d83837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
  have h2 (q : Pattern) (ha : d7435 q = 1) (hb : d83838 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d83838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7436 q = 1) (hb : d83839 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7436, d83839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7437 q = 1) (hb : d83840 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d83840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7438 q = 1) (hb : d83841 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d83841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q ha hb
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7515 q = 1) (hb : d83907 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, d83907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7515, d83907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14160 (p : Pattern) (ha : d7453 p = 1) (hb : d83856 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d83833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d83834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7452 q = 1) (hb : d83855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d83855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d83855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7453 q = 1) (hb : d83856 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, d83856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7453, d83856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14161 (p : Pattern) (ha : d7460 p = 1) (hb : d83863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d83833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7458 q = 1) (hb : d83861 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d83861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d83861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7459 q = 1) (hb : d83862 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d83862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7459, d83862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7460 q = 1) (hb : d83863 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, d83863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7460, d83863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14162 (p : Pattern) (ha : d83749 p = 1) (hb : d98845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d325 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d325, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
  have h2 (q : Pattern) (ha : d326 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d326, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d327 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d327, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6797 q = 1) (hb : d52127 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6797, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6797, d52127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83748 q = 1) (hb : d98844 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83748, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83748, d98844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83749 q = 1) (hb : d98845 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83749, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83749, d98845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14163 (p : Pattern) (ha : d83874 p = 1) (hb : d98851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d83869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d83869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10002 q ha hb
    | true =>
      simp only [d7466, d83869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d83870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d83870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d83870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83871 q = 1) (hb : d98848 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83871, d98848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83871, d98848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83872 q = 1) (hb : d98849 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83872, d98849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83872, d98849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83873 q = 1) (hb : d98850 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83873, d98850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83873, d98850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83874 q = 1) (hb : d98851 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83874, d98851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83874, d98851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14164 (p : Pattern) (ha : d83886 p = 1) (hb : d98857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7454 q = 1) (hb : d83857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d83857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14160 q ha hb
    | true =>
      simp only [d7454, d83857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d7455 q = 1) (hb : d83858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d83858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d83858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7456 q = 1) (hb : d83859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d83859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7456, d83859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7457 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d83860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d83860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7461 q = 1) (hb : d83864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d83864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14161 q ha hb
    | true =>
      simp only [d7461, d83864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d7462 q = 1) (hb : d83865 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d83865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d83865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7463 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d83866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7463, d83866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83875 q = 1) (hb : d98852 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83875, d98852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14163 q ha hb
    | true =>
      simp only [d83875, d98852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14155 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83876 q = 1) (hb : d98853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d98853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83876, d98853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7487 q = 1) (hb : d83881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d83881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9999 q ha hb
    | true =>
      simp only [d7487, d83881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7488 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d83882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7488, d83882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83883 q = 1) (hb : d98854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d98854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83883, d98854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83884 q = 1) (hb : d98855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d98855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83884, d98855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83885 q = 1) (hb : d98856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d98856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83885, d98856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83886 q = 1) (hb : d98857 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83886, d98857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83886, d98857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro14165 (p : Pattern) (ha : d7493 p = 1) (hb : d83887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d83833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7431 q = 1) (hb : d83834 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7431, d83834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7452 q = 1) (hb : d83855 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d83855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d83855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7493 q = 1) (hb : d83887 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, d83887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7493, d83887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14166 (p : Pattern) (ha : d7498 p = 1) (hb : d83892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7327 q = 1) (hb : d83750 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9977 q ha hb
    | true =>
      simp only [d7327, d83750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d83751 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d83751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7430 q = 1) (hb : d83833 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7430, d83833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7458 q = 1) (hb : d83861 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d83861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d83861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7459 q = 1) (hb : d83862 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d83862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7459, d83862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7498 q = 1) (hb : d83892 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, d83892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7498, d83892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14167 (p : Pattern) (ha : d83896 p = 1) (hb : d98858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7466 q = 1) (hb : d83869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7466, d83869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10002 q ha hb
    | true =>
      simp only [d7466, d83869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7467 q = 1) (hb : d83870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7467, d83870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7467, d83870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83750 q = 1) (hb : d98846 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14162 q ha hb
    | true =>
      simp only [d83750, d98846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83751 q = 1) (hb : d98847 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83751, d98847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83871 q = 1) (hb : d98848 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83871, d98848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83871, d98848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83872 q = 1) (hb : d98849 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83872, d98849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83872, d98849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83873 q = 1) (hb : d98850 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83873, d98850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83873, d98850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83896 q = 1) (hb : d98858 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83896, d98858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83896, d98858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14168 (p : Pattern) (ha : d83905 p = 1) (hb : d98864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7454 q = 1) (hb : d83857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d83857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14160 q ha hb
    | true =>
      simp only [d7454, d83857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro88 q ha hb
  have h2 (q : Pattern) (ha : d7455 q = 1) (hb : d83858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d83858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d83858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7456 q = 1) (hb : d83859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d83859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7456, d83859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7457 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d83860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d83860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7461 q = 1) (hb : d83864 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d83864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14161 q ha hb
    | true =>
      simp only [d7461, d83864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h6 (q : Pattern) (ha : d7462 q = 1) (hb : d83865 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d83865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d83865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7463 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d83866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7463, d83866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d83875 q = 1) (hb : d98852 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83875, d98852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14163 q ha hb
    | true =>
      simp only [d83875, d98852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14155 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83837 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d83876 q = 1) (hb : d98853 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d98853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83876, d98853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7487 q = 1) (hb : d83881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d83881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9999 q ha hb
    | true =>
      simp only [d7487, d83881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7488 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, d83882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7488, d83882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d83883 q = 1) (hb : d98854 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d98854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83883, d98854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83884 q = 1) (hb : d98855 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d98855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d83884, d98855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83885 q = 1) (hb : d98856 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d98856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83885, d98856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7494 q = 1) (hb : d83888 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, d83888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14165 q ha hb
    | true =>
      simp only [d7494, d83888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro94 q ha hb
  have h17 (q : Pattern) (ha : d7495 q = 1) (hb : d83889 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, d83889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7495, d83889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7496 q = 1) (hb : d83890 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, d83890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7496, d83890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7497 q = 1) (hb : d83891 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, d83891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7497, d83891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7499 q = 1) (hb : d83893 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, d83893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14166 q ha hb
    | true =>
      simp only [d7499, d83893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q ha hb
  have h21 (q : Pattern) (ha : d7500 q = 1) (hb : d83894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, d83894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7500, d83894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7501 q = 1) (hb : d83895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, d83895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7501, d83895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d83897 q = 1) (hb : d98859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83897, d98859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14167 q ha hb
    | true =>
      simp only [d83897, d98859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14157 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d83898 q = 1) (hb : d98860 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d98860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d83898, d98860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7508 q = 1) (hb : d83900 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d83900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10005 q ha hb
    | true =>
      simp only [d7508, d83900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7509 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d83901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7509, d83901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d83902 q = 1) (hb : d98861 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d98861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d83902, d98861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83903 q = 1) (hb : d98862 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83903, d98862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d83903, d98862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83904 q = 1) (hb : d98863 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83904, d98863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d83904, d98863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83905 q = 1) (hb : d98864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83905, d98864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83905, d98864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro14169 (p : Pattern) (ha : d83914 p = 1) (hb : d98871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83897 q = 1) (hb : d98859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83897, d98859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14167 q ha hb
    | true =>
      simp only [d83897, d98859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14157 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83846 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83898 q = 1) (hb : d98860 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d98860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83898, d98860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7508 q = 1) (hb : d83900 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d83900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10005 q ha hb
    | true =>
      simp only [d7508, d83900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7509 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, d83901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7509, d83901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83902 q = 1) (hb : d98861 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d98861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83902, d98861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83912 q = 1) (hb : d98869 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83912, d98869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83912, d98869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83913 q = 1) (hb : d98870 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83913, d98870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83913, d98870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83914 q = 1) (hb : d98871 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83914, d98871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83914, d98871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14170 (p : Pattern) (ha : d7539 p = 1) (hb : d83931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7391 q = 1) (hb : d83803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9990 q ha hb
    | true =>
      simp only [d7391, d83803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7392 q = 1) (hb : d83804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7392, d83804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71 q ha hb
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7536 q = 1) (hb : d83928 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d83928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7536, d83928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7537 q = 1) (hb : d83929 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d83929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7537, d83929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7538 q = 1) (hb : d83930 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d83930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7538, d83930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7539 q = 1) (hb : d83931 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d83931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7539, d83931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14171 (p : Pattern) (ha : d83802 p = 1) (hb : d98878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d418 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d418, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
  have h2 (q : Pattern) (ha : d419 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d419, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d420 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d420, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6843 q = 1) (hb : d52187 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6843, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6843, d52187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83801 q = 1) (hb : d98877 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83801, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83801, d98877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83802 q = 1) (hb : d98878 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83802, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83802, d98878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14172 (p : Pattern) (ha : d83927 p = 1) (hb : d98884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7530 q = 1) (hb : d83922 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7530, d83922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10014 q ha hb
    | true =>
      simp only [d7530, d83922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7531 q = 1) (hb : d83923 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7531, d83923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7531, d83923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83803 q = 1) (hb : d98879 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14171 q ha hb
    | true =>
      simp only [d83803, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83804 q = 1) (hb : d98880 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83804, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83924 q = 1) (hb : d98881 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d83924, d98881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83924, d98881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83925 q = 1) (hb : d98882 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d83925, d98882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83925, d98882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83926 q = 1) (hb : d98883 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d83926, d98883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83926, d98883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83927 q = 1) (hb : d98884 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d83927, d98884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83927, d98884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14173 (p : Pattern) (ha : d83944 p = 1) (hb : d98890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83932 q = 1) (hb : d98885 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83932, d98885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14172 q ha hb
    | true =>
      simp only [d83932, d98885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14170 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83934 q = 1) (hb : d98886 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83934, d98886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83934, d98886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7555 q = 1) (hb : d83939 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7555, d83939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10013 q ha hb
    | true =>
      simp only [d7555, d83939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7556 q = 1) (hb : d83940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7556, d83940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7556, d83940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d83941 q = 1) (hb : d98887 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83941, d98887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83941, d98887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83942 q = 1) (hb : d98888 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83942, d98888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83942, d98888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83943 q = 1) (hb : d98889 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83943, d98889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83943, d98889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83944 q = 1) (hb : d98890 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83944, d98890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83944, d98890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14174 (p : Pattern) (ha : d83950 p = 1) (hb : d98896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7440 q = 1) (hb : d83843 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, d83843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7440, d83843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14156 q ha hb
  have h2 (q : Pattern) (ha : d7441 q = 1) (hb : d83844 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, d83844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7441, d83844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7449 q = 1) (hb : d83852 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d83852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14156 q ha hb
    | true =>
      simp only [d7449, d83852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14158 q ha hb
  have h4 (q : Pattern) (ha : d7450 q = 1) (hb : d83853 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d83853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7450, d83853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7451 q = 1) (hb : d83854 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, d83854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7451, d83854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83906 q = 1) (hb : d98865 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83906, d98865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14164 q ha hb
    | true =>
      simp only [d83906, d98865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14168 q ha hb
  have h7 (q : Pattern) (ha : d7516 q = 1) (hb : d83908 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, d83908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14159 q ha hb
    | true =>
      simp only [d7516, d83908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69 q ha hb
  have h8 (q : Pattern) (ha : d83909 q = 1) (hb : d98866 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83909, d98866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83909, d98866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d83910 q = 1) (hb : d98867 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83910, d98867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83910, d98867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d83911 q = 1) (hb : d98868 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83911, d98868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83911, d98868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83915 q = 1) (hb : d98872 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83915, d98872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83915, d98872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14169 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro70 q ha hb
  have h13 (q : Pattern) (ha : d83916 q = 1) (hb : d98873 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83916, d98873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d83916, d98873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83917 q = 1) (hb : d98874 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83917, d98874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83917, d98874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83918 q = 1) (hb : d98875 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83918, d98875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d83918, d98875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83919 q = 1) (hb : d98876 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83919, d98876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83919, d98876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83945 q = 1) (hb : d98891 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83945, d98891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83945, d98891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14173 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro73 q ha hb
  have h19 (q : Pattern) (ha : d83946 q = 1) (hb : d98892 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83946, d98892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83946, d98892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d83947 q = 1) (hb : d98893 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83947, d98893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d83947, d98893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d83948 q = 1) (hb : d98894 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83948, d98894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d83948, d98894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83949 q = 1) (hb : d98895 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83949, d98895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d83949, d98895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83950 q = 1) (hb : d98896 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83950, d98896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83950, d98896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro14175 (p : Pattern) (ha : d83956 p = 1) (hb : d98902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83951 q = 1) (hb : d98897 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83951, d98897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83951, d98897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14174 q ha hb
  have h2 (q : Pattern) (ha : d83952 q = 1) (hb : d98898 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83952, d98898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83952, d98898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83953 q = 1) (hb : d98899 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83953, d98899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83953, d98899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83954 q = 1) (hb : d98900 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83954, d98900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83954, d98900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83955 q = 1) (hb : d98901 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83955, d98901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83955, d98901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83956 q = 1) (hb : d98902 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83956, d98902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83956, d98902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14176 (p : Pattern) (ha : d7581 p = 1) (hb : d83965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d83960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10019 q ha hb
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d83961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d83962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d83963 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7580 q = 1) (hb : d83964 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d83964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7580, d83964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7581 q = 1) (hb : d83965 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, d83965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7581, d83965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14177 (p : Pattern) (ha : d7587 p = 1) (hb : d83971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14176 q ha hb
    | true =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d83967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d83968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d83969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d83970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7587 q = 1) (hb : d83971 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d83971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d83971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14178 (p : Pattern) (ha : d7590 p = 1) (hb : d83974 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d83960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10019 q ha hb
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d83961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d83962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d83963 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7580 q = 1) (hb : d83964 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d83964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7580, d83964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7590 q = 1) (hb : d83974 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, d83974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7590, d83974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14179 (p : Pattern) (ha : d7596 p = 1) (hb : d83980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14176 q ha hb
    | true =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d83967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d83968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d83969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d83970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7591 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d83975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14178 q ha hb
    | true =>
      simp only [d7591, d83975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q ha hb
  have h7 (q : Pattern) (ha : d7592 q = 1) (hb : d83976 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d83976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d83976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7593 q = 1) (hb : d83977 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d83977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7593, d83977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7594 q = 1) (hb : d83978 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d83978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d83978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7595 q = 1) (hb : d83979 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d83979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d83979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7596 q = 1) (hb : d83980 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d83980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7596, d83980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14180 (p : Pattern) (ha : d7663 p = 1) (hb : d84036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7582 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14176 q ha hb
    | true =>
      simp only [d7582, d83966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
  have h2 (q : Pattern) (ha : d7583 q = 1) (hb : d83967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d83967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7584 q = 1) (hb : d83968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7584, d83968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7585 q = 1) (hb : d83969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d83969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7586 q = 1) (hb : d83970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d83970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q ha hb
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7663 q = 1) (hb : d84036 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, d84036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7663, d84036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14181 (p : Pattern) (ha : d7601 p = 1) (hb : d83985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d83960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10019 q ha hb
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d83961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d83962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d83963 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7600 q = 1) (hb : d83984 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d83984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d83984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7601 q = 1) (hb : d83985 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, d83985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7601, d83985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14182 (p : Pattern) (ha : d7608 p = 1) (hb : d83992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d83960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10019 q ha hb
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d83961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d83962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7606 q = 1) (hb : d83990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d83990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d83990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7607 q = 1) (hb : d83991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d83991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7607, d83991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7608 q = 1) (hb : d83992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, d83992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7608, d83992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14183 (p : Pattern) (ha : d83959 p = 1) (hb : d98905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d759 q = 1) (hb : d52436 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d759, d52436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
  have h2 (q : Pattern) (ha : d760 q = 1) (hb : d52437 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d52437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d761 q = 1) (hb : d52438 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d52438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6875 q = 1) (hb : d52443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6875, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6875, d52443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83958 q = 1) (hb : d98904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d83958, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d83958, d98904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83959 q = 1) (hb : d98905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d83959, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83959, d98905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14184 (p : Pattern) (ha : d84003 p = 1) (hb : d98911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d83998 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d83998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10027 q ha hb
    | true =>
      simp only [d7614, d83998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d83999 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d83999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d83999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84000 q = 1) (hb : d98908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84000, d98908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84000, d98908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84001 q = 1) (hb : d98909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84001, d98909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84001, d98909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84002 q = 1) (hb : d98910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84002, d98910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84002, d98910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84003 q = 1) (hb : d98911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84003, d98911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84003, d98911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14185 (p : Pattern) (ha : d84015 p = 1) (hb : d98917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7602 q = 1) (hb : d83986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d83986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14181 q ha hb
    | true =>
      simp only [d7602, d83986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d7603 q = 1) (hb : d83987 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d83987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d83987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7604 q = 1) (hb : d83988 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d83988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7604, d83988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7605 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d83989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d83989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7609 q = 1) (hb : d83993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d83993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14182 q ha hb
    | true =>
      simp only [d7609, d83993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d7610 q = 1) (hb : d83994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d83994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d83994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7611 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d83995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7611, d83995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d84004 q = 1) (hb : d98912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84004, d98912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14184 q ha hb
    | true =>
      simp only [d84004, d98912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14176 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84005 q = 1) (hb : d98913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d98913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84005, d98913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7635 q = 1) (hb : d84010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d84010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10024 q ha hb
    | true =>
      simp only [d7635, d84010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7636 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d84011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7636, d84011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d84012 q = 1) (hb : d98914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d98914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84012, d98914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84013 q = 1) (hb : d98915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d98915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d84013, d98915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84014 q = 1) (hb : d98916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d98916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84014, d98916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84015 q = 1) (hb : d98917 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84015, d98917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84015, d98917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro14186 (p : Pattern) (ha : d7641 p = 1) (hb : d84016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d83960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10019 q ha hb
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d83961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d83962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7579 q = 1) (hb : d83963 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7579, d83963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7600 q = 1) (hb : d83984 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d83984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d83984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7641 q = 1) (hb : d84016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, d84016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7641, d84016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14187 (p : Pattern) (ha : d7646 p = 1) (hb : d84021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7576 q = 1) (hb : d83960 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10019 q ha hb
    | true =>
      simp only [d7576, d83960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d83961 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d83961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7578 q = 1) (hb : d83962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7578, d83962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7606 q = 1) (hb : d83990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d83990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d83990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7607 q = 1) (hb : d83991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d83991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7607, d83991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7646 q = 1) (hb : d84021 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, d84021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7646, d84021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14188 (p : Pattern) (ha : d84025 p = 1) (hb : d98918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7614 q = 1) (hb : d83998 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7614, d83998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10027 q ha hb
    | true =>
      simp only [d7614, d83998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7615 q = 1) (hb : d83999 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7615, d83999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7615, d83999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83960 q = 1) (hb : d98906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14183 q ha hb
    | true =>
      simp only [d83960, d98906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83961 q = 1) (hb : d98907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83961, d98907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84000 q = 1) (hb : d98908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84000, d98908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84000, d98908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84001 q = 1) (hb : d98909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84001, d98909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84001, d98909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84002 q = 1) (hb : d98910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84002, d98910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84002, d98910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84025 q = 1) (hb : d98918 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84025, d98918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84025, d98918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14189 (p : Pattern) (ha : d84034 p = 1) (hb : d98924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7602 q = 1) (hb : d83986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d83986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14181 q ha hb
    | true =>
      simp only [d7602, d83986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro135 q ha hb
  have h2 (q : Pattern) (ha : d7603 q = 1) (hb : d83987 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d83987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d83987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7604 q = 1) (hb : d83988 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d83988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7604, d83988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7605 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d83989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d83989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7609 q = 1) (hb : d83993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d83993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14182 q ha hb
    | true =>
      simp only [d7609, d83993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h6 (q : Pattern) (ha : d7610 q = 1) (hb : d83994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d83994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d83994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7611 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d83995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7611, d83995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d84004 q = 1) (hb : d98912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84004, d98912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14184 q ha hb
    | true =>
      simp only [d84004, d98912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14176 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83966 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84005 q = 1) (hb : d98913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d98913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84005, d98913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7635 q = 1) (hb : d84010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d84010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10024 q ha hb
    | true =>
      simp only [d7635, d84010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7636 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, d84011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7636, d84011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d84012 q = 1) (hb : d98914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d98914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84012, d98914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84013 q = 1) (hb : d98915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d98915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d84013, d98915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84014 q = 1) (hb : d98916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d98916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84014, d98916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7642 q = 1) (hb : d84017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, d84017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14186 q ha hb
    | true =>
      simp only [d7642, d84017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro141 q ha hb
  have h17 (q : Pattern) (ha : d7643 q = 1) (hb : d84018 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, d84018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7643, d84018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7644 q = 1) (hb : d84019 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, d84019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7644, d84019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7645 q = 1) (hb : d84020 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, d84020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7645, d84020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7647 q = 1) (hb : d84022 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, d84022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14187 q ha hb
    | true =>
      simp only [d7647, d84022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q ha hb
  have h21 (q : Pattern) (ha : d7648 q = 1) (hb : d84023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, d84023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7648, d84023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7649 q = 1) (hb : d84024 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, d84024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7649, d84024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d84026 q = 1) (hb : d98919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84026, d98919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14188 q ha hb
    | true =>
      simp only [d84026, d98919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14178 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84027 q = 1) (hb : d98920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d98920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84027, d98920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7656 q = 1) (hb : d84029 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d84029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10030 q ha hb
    | true =>
      simp only [d7656, d84029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7657 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d84030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7657, d84030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d84031 q = 1) (hb : d98921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d98921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84031, d98921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d84032 q = 1) (hb : d98922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84032, d98922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d84032, d98922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84033 q = 1) (hb : d98923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84033, d98923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d84033, d98923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84034 q = 1) (hb : d98924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84034, d98924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84034, d98924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro14190 (p : Pattern) (ha : d84043 p = 1) (hb : d98931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84026 q = 1) (hb : d98919 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84026, d98919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14188 q ha hb
    | true =>
      simp only [d84026, d98919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14178 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84027 q = 1) (hb : d98920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d98920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84027, d98920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7656 q = 1) (hb : d84029 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d84029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10030 q ha hb
    | true =>
      simp only [d7656, d84029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7657 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, d84030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7657, d84030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d84031 q = 1) (hb : d98921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d98921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84031, d98921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84041 q = 1) (hb : d98929 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84041, d98929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84041, d98929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84042 q = 1) (hb : d98930 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84042, d98930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84042, d98930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84043 q = 1) (hb : d98931 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84043, d98931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84043, d98931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14191 (p : Pattern) (ha : d7691 p = 1) (hb : d84064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7682 q = 1) (hb : d84055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d84055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10037 q ha hb
    | true =>
      simp only [d7682, d84055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7683 q = 1) (hb : d84056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d84056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7683, d84056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7688 q = 1) (hb : d84061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, d84061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7688, d84061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7689 q = 1) (hb : d84062 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, d84062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7689, d84062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7690 q = 1) (hb : d84063 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, d84063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7690, d84063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7691 q = 1) (hb : d84064 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, d84064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7691, d84064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14192 (p : Pattern) (ha : d84054 p = 1) (hb : d98938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d982 q = 1) (hb : d52601 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
    | true =>
      simp only [d982, d52601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
  have h2 (q : Pattern) (ha : d983 q = 1) (hb : d52602 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d52602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d984 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d52603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52608 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6921 q = 1) (hb : d52609 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6921, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6921, d52609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84053 q = 1) (hb : d98937 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84053, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84053, d98937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84054 q = 1) (hb : d98938 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84054, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84054, d98938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14193 (p : Pattern) (ha : d84060 p = 1) (hb : d98944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7678 q = 1) (hb : d84051 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7678, d84051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10040 q ha hb
    | true =>
      simp only [d7678, d84051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7679 q = 1) (hb : d84052 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7679, d84052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7679, d84052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84055 q = 1) (hb : d98939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14192 q ha hb
    | true =>
      simp only [d84055, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84056 q = 1) (hb : d98940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84057 q = 1) (hb : d98941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84057, d98941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84057, d98941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84058 q = 1) (hb : d98942 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84058, d98942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84058, d98942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84059 q = 1) (hb : d98943 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84059, d98943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84059, d98943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84060 q = 1) (hb : d98944 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84060, d98944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84060, d98944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14194 (p : Pattern) (ha : d84077 p = 1) (hb : d98950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84065 q = 1) (hb : d98945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84065, d98945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14193 q ha hb
    | true =>
      simp only [d84065, d98945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14191 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84066 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84067 q = 1) (hb : d98946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84067, d98946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84067, d98946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7707 q = 1) (hb : d84072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7707, d84072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10039 q ha hb
    | true =>
      simp only [d7707, d84072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7708 q = 1) (hb : d84073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7708, d84073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7708, d84073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d84074 q = 1) (hb : d98947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84074, d98947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84074, d98947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84075 q = 1) (hb : d98948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84075, d98948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84075, d98948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84076 q = 1) (hb : d98949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84076, d98949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84076, d98949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84077 q = 1) (hb : d98950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84077, d98950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84077, d98950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14195 (p : Pattern) (ha : d84083 p = 1) (hb : d98956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7588 q = 1) (hb : d83972 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, d83972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7588, d83972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14177 q ha hb
  have h2 (q : Pattern) (ha : d7589 q = 1) (hb : d83973 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, d83973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7589, d83973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7597 q = 1) (hb : d83981 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d83981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14177 q ha hb
    | true =>
      simp only [d7597, d83981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14179 q ha hb
  have h4 (q : Pattern) (ha : d7598 q = 1) (hb : d83982 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d83982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7598, d83982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7599 q = 1) (hb : d83983 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, d83983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7599, d83983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84035 q = 1) (hb : d98925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84035, d98925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14185 q ha hb
    | true =>
      simp only [d84035, d98925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14189 q ha hb
  have h7 (q : Pattern) (ha : d7664 q = 1) (hb : d84037 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, d84037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14180 q ha hb
    | true =>
      simp only [d7664, d84037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q ha hb
  have h8 (q : Pattern) (ha : d84038 q = 1) (hb : d98926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84038, d98926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84038, d98926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d84039 q = 1) (hb : d98927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84039, d98927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84039, d98927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84040 q = 1) (hb : d98928 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84040, d98928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84040, d98928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84044 q = 1) (hb : d98932 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84044, d98932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84044, d98932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14190 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro114 q ha hb
  have h13 (q : Pattern) (ha : d84045 q = 1) (hb : d98933 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84045, d98933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84045, d98933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84046 q = 1) (hb : d98934 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84046, d98934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84046, d98934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84047 q = 1) (hb : d98935 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84047, d98935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84047, d98935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84048 q = 1) (hb : d98936 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84048, d98936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84048, d98936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84078 q = 1) (hb : d98951 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84078, d98951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84078, d98951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14194 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro119 q ha hb
  have h19 (q : Pattern) (ha : d84079 q = 1) (hb : d98952 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84079, d98952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84079, d98952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84080 q = 1) (hb : d98953 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84080, d98953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84080, d98953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84081 q = 1) (hb : d98954 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84081, d98954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84081, d98954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84082 q = 1) (hb : d98955 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84082, d98955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84082, d98955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84083 q = 1) (hb : d98956 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84083, d98956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84083, d98956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro14196 (p : Pattern) (ha : d84089 p = 1) (hb : d98962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84084 q = 1) (hb : d98957 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84084, d98957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84084, d98957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14195 q ha hb
  have h2 (q : Pattern) (ha : d84085 q = 1) (hb : d98958 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84085, d98958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84085, d98958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84086 q = 1) (hb : d98959 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84086, d98959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84086, d98959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84087 q = 1) (hb : d98960 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84087, d98960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84087, d98960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84088 q = 1) (hb : d98961 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84088, d98961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84088, d98961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84089 q = 1) (hb : d98962 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84089, d98962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84089, d98962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14197 (p : Pattern) (ha : d7734 p = 1) (hb : d84099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d84094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10045 q ha hb
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d84095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d84096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d84097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7733 q = 1) (hb : d84098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d84098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7733, d84098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7734 q = 1) (hb : d84099 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, d84099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7734, d84099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14198 (p : Pattern) (ha : d7740 p = 1) (hb : d84105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14197 q ha hb
    | true =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d84101 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d84102 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d84103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d84104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7740 q = 1) (hb : d84105 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d84105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d84105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14199 (p : Pattern) (ha : d7743 p = 1) (hb : d84108 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d84094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10045 q ha hb
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d84095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d84096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d84097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7733 q = 1) (hb : d84098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d84098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7733, d84098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7743 q = 1) (hb : d84108 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, d84108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7743, d84108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14200 (p : Pattern) (ha : d7749 p = 1) (hb : d84114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14197 q ha hb
    | true =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d84101 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d84102 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d84103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d84104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7744 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d84109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14199 q ha hb
    | true =>
      simp only [d7744, d84109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q ha hb
  have h7 (q : Pattern) (ha : d7745 q = 1) (hb : d84110 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d84110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d84110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7746 q = 1) (hb : d84111 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d84111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7746, d84111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7747 q = 1) (hb : d84112 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d84112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d84112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7748 q = 1) (hb : d84113 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d84113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d84113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7749 q = 1) (hb : d84114 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d84114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7749, d84114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14201 (p : Pattern) (ha : d7816 p = 1) (hb : d84170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7735 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14197 q ha hb
    | true =>
      simp only [d7735, d84100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
  have h2 (q : Pattern) (ha : d7736 q = 1) (hb : d84101 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d84101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7737 q = 1) (hb : d84102 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7737, d84102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7738 q = 1) (hb : d84103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d84103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7739 q = 1) (hb : d84104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d84104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7816 q = 1) (hb : d84170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, d84170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7816, d84170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14202 (p : Pattern) (ha : d7754 p = 1) (hb : d84119 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d84094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10045 q ha hb
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d84095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d84096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d84097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7753 q = 1) (hb : d84118 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d84118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d84118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7754 q = 1) (hb : d84119 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, d84119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7754, d84119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14203 (p : Pattern) (ha : d7761 p = 1) (hb : d84126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d84094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10045 q ha hb
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d84095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d84096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7759 q = 1) (hb : d84124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d84124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d84124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7760 q = 1) (hb : d84125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d84125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7760, d84125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7761 q = 1) (hb : d84126 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, d84126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7761, d84126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14204 (p : Pattern) (ha : d84093 p = 1) (hb : d98966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1129 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
  have h2 (q : Pattern) (ha : d1130 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1131 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d6954 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6954, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6954, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84092 q = 1) (hb : d98965 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84092, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84092, d98965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84093 q = 1) (hb : d98966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84093, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84093, d98966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14205 (p : Pattern) (ha : d84137 p = 1) (hb : d98972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d84132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d84132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10053 q ha hb
    | true =>
      simp only [d7767, d84132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d84133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d84133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d84133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84134 q = 1) (hb : d98969 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84134, d98969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84134, d98969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84135 q = 1) (hb : d98970 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84135, d98970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84135, d98970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84136 q = 1) (hb : d98971 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84136, d98971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84136, d98971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84137 q = 1) (hb : d98972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84137, d98972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84137, d98972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14206 (p : Pattern) (ha : d84149 p = 1) (hb : d98978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7755 q = 1) (hb : d84120 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d84120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14202 q ha hb
    | true =>
      simp only [d7755, d84120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d7756 q = 1) (hb : d84121 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d84121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d84121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7757 q = 1) (hb : d84122 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d84122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7757, d84122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7758 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d84123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d84123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7762 q = 1) (hb : d84127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d84127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14203 q ha hb
    | true =>
      simp only [d7762, d84127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d7763 q = 1) (hb : d84128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d84128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d84128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7764 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d84129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7764, d84129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d84138 q = 1) (hb : d98973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84138, d98973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14205 q ha hb
    | true =>
      simp only [d84138, d98973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14197 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84139 q = 1) (hb : d98974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d98974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84139, d98974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7788 q = 1) (hb : d84144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d84144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10050 q ha hb
    | true =>
      simp only [d7788, d84144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7789 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d84145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7789, d84145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d84146 q = 1) (hb : d98975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d98975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84146, d98975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84147 q = 1) (hb : d98976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d98976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d84147, d98976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84148 q = 1) (hb : d98977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d98977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84148, d98977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84149 q = 1) (hb : d98978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84149, d98978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84149, d98978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro14207 (p : Pattern) (ha : d7794 p = 1) (hb : d84150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d84094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10045 q ha hb
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d84095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d84096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7732 q = 1) (hb : d84097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7732, d84097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7753 q = 1) (hb : d84118 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d84118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d84118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7794 q = 1) (hb : d84150 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, d84150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7794, d84150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14208 (p : Pattern) (ha : d7799 p = 1) (hb : d84155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7729 q = 1) (hb : d84094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10045 q ha hb
    | true =>
      simp only [d7729, d84094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d84095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d84095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7731 q = 1) (hb : d84096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7731, d84096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7759 q = 1) (hb : d84124 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d84124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d84124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7760 q = 1) (hb : d84125 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d84125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7760, d84125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7799 q = 1) (hb : d84155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, d84155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7799, d84155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14209 (p : Pattern) (ha : d84159 p = 1) (hb : d98979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7767 q = 1) (hb : d84132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7767, d84132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10053 q ha hb
    | true =>
      simp only [d7767, d84132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7768 q = 1) (hb : d84133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7768, d84133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7768, d84133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84134 q = 1) (hb : d98969 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84134, d98969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84134, d98969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84135 q = 1) (hb : d98970 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84135, d98970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84135, d98970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84136 q = 1) (hb : d98971 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84136, d98971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84136, d98971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84159 q = 1) (hb : d98979 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84159, d98979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84159, d98979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14210 (p : Pattern) (ha : d84168 p = 1) (hb : d98985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7755 q = 1) (hb : d84120 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d84120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14202 q ha hb
    | true =>
      simp only [d7755, d84120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q ha hb
  have h2 (q : Pattern) (ha : d7756 q = 1) (hb : d84121 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d84121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d84121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7757 q = 1) (hb : d84122 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d84122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7757, d84122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7758 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d84123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d84123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7762 q = 1) (hb : d84127 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d84127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14203 q ha hb
    | true =>
      simp only [d7762, d84127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h6 (q : Pattern) (ha : d7763 q = 1) (hb : d84128 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d84128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d84128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7764 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d84129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7764, d84129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d84138 q = 1) (hb : d98973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84138, d98973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14205 q ha hb
    | true =>
      simp only [d84138, d98973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14197 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84139 q = 1) (hb : d98974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d98974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84139, d98974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7788 q = 1) (hb : d84144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d84144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10050 q ha hb
    | true =>
      simp only [d7788, d84144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7789 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, d84145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7789, d84145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d84146 q = 1) (hb : d98975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d98975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84146, d98975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84147 q = 1) (hb : d98976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d98976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d84147, d98976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84148 q = 1) (hb : d98977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d98977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84148, d98977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7795 q = 1) (hb : d84151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, d84151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14207 q ha hb
    | true =>
      simp only [d7795, d84151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q ha hb
  have h17 (q : Pattern) (ha : d7796 q = 1) (hb : d84152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, d84152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7796, d84152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7797 q = 1) (hb : d84153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, d84153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7797, d84153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7798 q = 1) (hb : d84154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, d84154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7798, d84154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7800 q = 1) (hb : d84156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, d84156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14208 q ha hb
    | true =>
      simp only [d7800, d84156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q ha hb
  have h21 (q : Pattern) (ha : d7801 q = 1) (hb : d84157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, d84157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7801, d84157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7802 q = 1) (hb : d84158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, d84158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7802, d84158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d84160 q = 1) (hb : d98980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84160, d98980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14209 q ha hb
    | true =>
      simp only [d84160, d98980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14199 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84161 q = 1) (hb : d98981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d98981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84161, d98981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7809 q = 1) (hb : d84163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d84163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10056 q ha hb
    | true =>
      simp only [d7809, d84163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7810 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d84164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7810, d84164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d84165 q = 1) (hb : d98982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d98982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84165, d98982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d84166 q = 1) (hb : d98983 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84166, d98983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d84166, d98983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84167 q = 1) (hb : d98984 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84167, d98984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d84167, d98984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84168 q = 1) (hb : d98985 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84168, d98985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84168, d98985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro14211 (p : Pattern) (ha : d84177 p = 1) (hb : d98992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84160 q = 1) (hb : d98980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84160, d98980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14209 q ha hb
    | true =>
      simp only [d84160, d98980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14199 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84161 q = 1) (hb : d98981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d98981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84161, d98981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7809 q = 1) (hb : d84163 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d84163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10056 q ha hb
    | true =>
      simp only [d7809, d84163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7810 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, d84164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7810, d84164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d84165 q = 1) (hb : d98982 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d98982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84165, d98982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84175 q = 1) (hb : d98990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84175, d98990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84175, d98990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84176 q = 1) (hb : d98991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84176, d98991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84176, d98991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84177 q = 1) (hb : d98992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84177, d98992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84177, d98992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14212 (p : Pattern) (ha : d7844 p = 1) (hb : d84198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7835 q = 1) (hb : d84189 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d84189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10063 q ha hb
    | true =>
      simp only [d7835, d84189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7836 q = 1) (hb : d84190 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d84190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7836, d84190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7841 q = 1) (hb : d84195 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, d84195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7841, d84195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7842 q = 1) (hb : d84196 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, d84196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7842, d84196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7843 q = 1) (hb : d84197 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, d84197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7843, d84197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7844 q = 1) (hb : d84198 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, d84198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7844, d84198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14213 (p : Pattern) (ha : d84188 p = 1) (hb : d98999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1402 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
  have h2 (q : Pattern) (ha : d1403 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1404 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7000 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7000, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7000, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84187 q = 1) (hb : d98998 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84187, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84187, d98998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84188 q = 1) (hb : d98999 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84188, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84188, d98999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14214 (p : Pattern) (ha : d84194 p = 1) (hb : d99005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7831 q = 1) (hb : d84185 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7831, d84185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10066 q ha hb
    | true =>
      simp only [d7831, d84185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7832 q = 1) (hb : d84186 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7832, d84186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7832, d84186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84189 q = 1) (hb : d99000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14213 q ha hb
    | true =>
      simp only [d84189, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84190 q = 1) (hb : d99001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84191 q = 1) (hb : d99002 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84191, d99002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84191, d99002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84192 q = 1) (hb : d99003 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84192, d99003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84192, d99003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84193 q = 1) (hb : d99004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84193, d99004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84193, d99004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84194 q = 1) (hb : d99005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84194, d99005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84194, d99005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14215 (p : Pattern) (ha : d84211 p = 1) (hb : d99011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84199 q = 1) (hb : d99006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84199, d99006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14214 q ha hb
    | true =>
      simp only [d84199, d99006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14212 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84201 q = 1) (hb : d99007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84201, d99007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84201, d99007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7860 q = 1) (hb : d84206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7860, d84206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10065 q ha hb
    | true =>
      simp only [d7860, d84206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7861 q = 1) (hb : d84207 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7861, d84207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7861, d84207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d84208 q = 1) (hb : d99008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84208, d99008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84208, d99008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84209 q = 1) (hb : d99009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84209, d99009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84209, d99009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84210 q = 1) (hb : d99010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84210, d99010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84210, d99010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84211 q = 1) (hb : d99011 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84211, d99011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84211, d99011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14216 (p : Pattern) (ha : d84217 p = 1) (hb : d99017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7741 q = 1) (hb : d84106 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, d84106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7741, d84106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14198 q ha hb
  have h2 (q : Pattern) (ha : d7742 q = 1) (hb : d84107 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, d84107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7742, d84107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7750 q = 1) (hb : d84115 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d84115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14198 q ha hb
    | true =>
      simp only [d7750, d84115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14200 q ha hb
  have h4 (q : Pattern) (ha : d7751 q = 1) (hb : d84116 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d84116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7751, d84116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7752 q = 1) (hb : d84117 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, d84117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7752, d84117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84169 q = 1) (hb : d98986 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84169, d98986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14206 q ha hb
    | true =>
      simp only [d84169, d98986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14210 q ha hb
  have h7 (q : Pattern) (ha : d7817 q = 1) (hb : d84171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, d84171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14201 q ha hb
    | true =>
      simp only [d7817, d84171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q ha hb
  have h8 (q : Pattern) (ha : d84172 q = 1) (hb : d98987 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84172, d98987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84172, d98987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d84173 q = 1) (hb : d98988 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84173, d98988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84173, d98988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84174 q = 1) (hb : d98989 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84174, d98989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84174, d98989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84178 q = 1) (hb : d98993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84178, d98993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84178, d98993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14211 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro166 q ha hb
  have h13 (q : Pattern) (ha : d84179 q = 1) (hb : d98994 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84179, d98994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84179, d98994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84180 q = 1) (hb : d98995 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84180, d98995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84180, d98995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84181 q = 1) (hb : d98996 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84181, d98996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84181, d98996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84182 q = 1) (hb : d98997 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84182, d98997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84182, d98997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84212 q = 1) (hb : d99012 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84212, d99012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84212, d99012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14215 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro171 q ha hb
  have h19 (q : Pattern) (ha : d84213 q = 1) (hb : d99013 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84213, d99013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84213, d99013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84214 q = 1) (hb : d99014 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84214, d99014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84214, d99014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84215 q = 1) (hb : d99015 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84215, d99015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84215, d99015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84216 q = 1) (hb : d99016 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84216, d99016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84216, d99016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84217 q = 1) (hb : d99017 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84217, d99017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84217, d99017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro14217 (p : Pattern) (ha : d84223 p = 1) (hb : d99023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84218 q = 1) (hb : d99018 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84218, d99018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84218, d99018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14216 q ha hb
  have h2 (q : Pattern) (ha : d84219 q = 1) (hb : d99019 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84219, d99019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84219, d99019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84220 q = 1) (hb : d99020 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84220, d99020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84220, d99020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84221 q = 1) (hb : d99021 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84221, d99021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84221, d99021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84222 q = 1) (hb : d99022 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84222, d99022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84222, d99022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84223 q = 1) (hb : d99023 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84223, d99023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84223, d99023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14218 (p : Pattern) (ha : d7888 p = 1) (hb : d84234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d84229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10071 q ha hb
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d84230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d84231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d84232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7887 q = 1) (hb : d84233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d84233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7887, d84233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7888 q = 1) (hb : d84234 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, d84234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7888, d84234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14219 (p : Pattern) (ha : d7894 p = 1) (hb : d84240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14218 q ha hb
    | true =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d84236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d84237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d84238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d84239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7894 q = 1) (hb : d84240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d84240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d84240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14220 (p : Pattern) (ha : d7897 p = 1) (hb : d84243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d84229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10071 q ha hb
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d84230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d84231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d84232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7887 q = 1) (hb : d84233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d84233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7887, d84233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7897 q = 1) (hb : d84243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, d84243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7897, d84243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14221 (p : Pattern) (ha : d7903 p = 1) (hb : d84249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14218 q ha hb
    | true =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d84236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d84237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d84238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d84239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7898 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d84244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14220 q ha hb
    | true =>
      simp only [d7898, d84244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q ha hb
  have h7 (q : Pattern) (ha : d7899 q = 1) (hb : d84245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d84245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d84245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7900 q = 1) (hb : d84246 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d84246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7900, d84246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d7901 q = 1) (hb : d84247 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d84247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d84247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7902 q = 1) (hb : d84248 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d84248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d84248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7903 q = 1) (hb : d84249 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d84249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7903, d84249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14222 (p : Pattern) (ha : d7970 p = 1) (hb : d84305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7889 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14218 q ha hb
    | true =>
      simp only [d7889, d84235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
  have h2 (q : Pattern) (ha : d7890 q = 1) (hb : d84236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d84236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7891 q = 1) (hb : d84237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7891, d84237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7892 q = 1) (hb : d84238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d84238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7893 q = 1) (hb : d84239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d84239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d7970 q = 1) (hb : d84305 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, d84305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7970, d84305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14223 (p : Pattern) (ha : d7908 p = 1) (hb : d84254 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d84229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10071 q ha hb
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d84230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d84231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d84232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7907 q = 1) (hb : d84253 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d84253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d84253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7908 q = 1) (hb : d84254 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, d84254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7908, d84254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14224 (p : Pattern) (ha : d7915 p = 1) (hb : d84261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d84229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10071 q ha hb
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d84230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d84231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7913 q = 1) (hb : d84259 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d84259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d84259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7914 q = 1) (hb : d84260 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d84260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7914, d84260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7915 q = 1) (hb : d84261 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, d84261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7915, d84261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14225 (p : Pattern) (ha : d84228 p = 1) (hb : d99028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1590 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
  have h2 (q : Pattern) (ha : d1591 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1592 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7034 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7034, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7034, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84227 q = 1) (hb : d99027 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84227, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84227, d99027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84228 q = 1) (hb : d99028 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84228, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84228, d99028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14226 (p : Pattern) (ha : d84272 p = 1) (hb : d99034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d84267 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d84267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10079 q ha hb
    | true =>
      simp only [d7921, d84267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d84268 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d84268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d84268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84269 q = 1) (hb : d99031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84269, d99031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84269, d99031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84270 q = 1) (hb : d99032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84270, d99032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84270, d99032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84271 q = 1) (hb : d99033 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84271, d99033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84271, d99033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84272 q = 1) (hb : d99034 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84272, d99034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84272, d99034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14227 (p : Pattern) (ha : d84284 p = 1) (hb : d99040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7909 q = 1) (hb : d84255 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d84255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14223 q ha hb
    | true =>
      simp only [d7909, d84255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d7910 q = 1) (hb : d84256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d84256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d84256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7911 q = 1) (hb : d84257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d84257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7911, d84257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7912 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d84258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d84258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7916 q = 1) (hb : d84262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d84262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14224 q ha hb
    | true =>
      simp only [d7916, d84262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d7917 q = 1) (hb : d84263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d84263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d84263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7918 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d84264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7918, d84264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d84273 q = 1) (hb : d99035 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84273, d99035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14226 q ha hb
    | true =>
      simp only [d84273, d99035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14218 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84274 q = 1) (hb : d99036 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d99036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84274, d99036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7942 q = 1) (hb : d84279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d84279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10076 q ha hb
    | true =>
      simp only [d7942, d84279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7943 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d84280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7943, d84280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d84281 q = 1) (hb : d99037 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d99037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84281, d99037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84282 q = 1) (hb : d99038 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d99038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d84282, d99038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84283 q = 1) (hb : d99039 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d99039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84283, d99039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84284 q = 1) (hb : d99040 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84284, d99040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84284, d99040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro14228 (p : Pattern) (ha : d7948 p = 1) (hb : d84285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d84229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10071 q ha hb
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d84230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d84231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7886 q = 1) (hb : d84232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7886, d84232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7907 q = 1) (hb : d84253 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d84253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d84253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7948 q = 1) (hb : d84285 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, d84285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7948, d84285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14229 (p : Pattern) (ha : d7953 p = 1) (hb : d84290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7883 q = 1) (hb : d84229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10071 q ha hb
    | true =>
      simp only [d7883, d84229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d84230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d84230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7885 q = 1) (hb : d84231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7885, d84231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7913 q = 1) (hb : d84259 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d84259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d84259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7914 q = 1) (hb : d84260 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d84260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7914, d84260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7953 q = 1) (hb : d84290 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, d84290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7953, d84290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14230 (p : Pattern) (ha : d84294 p = 1) (hb : d99041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7921 q = 1) (hb : d84267 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7921, d84267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10079 q ha hb
    | true =>
      simp only [d7921, d84267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7922 q = 1) (hb : d84268 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7922, d84268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7922, d84268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84269 q = 1) (hb : d99031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84269, d99031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84269, d99031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84270 q = 1) (hb : d99032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84270, d99032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84270, d99032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84271 q = 1) (hb : d99033 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84271, d99033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84271, d99033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84294 q = 1) (hb : d99041 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84294, d99041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84294, d99041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14231 (p : Pattern) (ha : d84303 p = 1) (hb : d99047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7909 q = 1) (hb : d84255 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d84255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14223 q ha hb
    | true =>
      simp only [d7909, d84255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q ha hb
  have h2 (q : Pattern) (ha : d7910 q = 1) (hb : d84256 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d84256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d84256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7911 q = 1) (hb : d84257 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d84257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7911, d84257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d7912 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d84258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d84258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7916 q = 1) (hb : d84262 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d84262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14224 q ha hb
    | true =>
      simp only [d7916, d84262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h6 (q : Pattern) (ha : d7917 q = 1) (hb : d84263 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d84263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d84263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7918 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d84264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7918, d84264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d84273 q = 1) (hb : d99035 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84273, d99035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14226 q ha hb
    | true =>
      simp only [d84273, d99035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14218 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84274 q = 1) (hb : d99036 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d99036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84274, d99036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d7942 q = 1) (hb : d84279 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d84279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10076 q ha hb
    | true =>
      simp only [d7942, d84279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d7943 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, d84280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d7943, d84280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d84281 q = 1) (hb : d99037 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d99037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84281, d99037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84282 q = 1) (hb : d99038 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d99038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d84282, d99038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84283 q = 1) (hb : d99039 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d99039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84283, d99039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d7949 q = 1) (hb : d84286 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, d84286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14228 q ha hb
    | true =>
      simp only [d7949, d84286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q ha hb
  have h17 (q : Pattern) (ha : d7950 q = 1) (hb : d84287 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, d84287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7950, d84287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7951 q = 1) (hb : d84288 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, d84288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d7951, d84288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d7952 q = 1) (hb : d84289 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, d84289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7952, d84289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d7954 q = 1) (hb : d84291 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, d84291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14229 q ha hb
    | true =>
      simp only [d7954, d84291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q ha hb
  have h21 (q : Pattern) (ha : d7955 q = 1) (hb : d84292 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, d84292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7955, d84292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7956 q = 1) (hb : d84293 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, d84293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7956, d84293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d84295 q = 1) (hb : d99042 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84295, d99042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14230 q ha hb
    | true =>
      simp only [d84295, d99042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14220 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84296 q = 1) (hb : d99043 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d99043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84296, d99043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7963 q = 1) (hb : d84298 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d84298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10082 q ha hb
    | true =>
      simp only [d7963, d84298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d7964 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d84299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7964, d84299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d84300 q = 1) (hb : d99044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d99044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84300, d99044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d84301 q = 1) (hb : d99045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84301, d99045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d84301, d99045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84302 q = 1) (hb : d99046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84302, d99046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d84302, d99046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84303 q = 1) (hb : d99047 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84303, d99047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84303, d99047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro14232 (p : Pattern) (ha : d84312 p = 1) (hb : d99054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84295 q = 1) (hb : d99042 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84295, d99042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14230 q ha hb
    | true =>
      simp only [d84295, d99042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14220 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84296 q = 1) (hb : d99043 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d99043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84296, d99043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7963 q = 1) (hb : d84298 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d84298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10082 q ha hb
    | true =>
      simp only [d7963, d84298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7964 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, d84299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7964, d84299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d84300 q = 1) (hb : d99044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d99044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84300, d99044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84310 q = 1) (hb : d99052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84310, d99052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84310, d99052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84311 q = 1) (hb : d99053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84311, d99053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84311, d99053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84312 q = 1) (hb : d99054 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84312, d99054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84312, d99054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14233 (p : Pattern) (ha : d7998 p = 1) (hb : d84333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7989 q = 1) (hb : d84324 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d84324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10089 q ha hb
    | true =>
      simp only [d7989, d84324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7990 q = 1) (hb : d84325 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d84325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7990, d84325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7995 q = 1) (hb : d84330 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, d84330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7995, d84330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7996 q = 1) (hb : d84331 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, d84331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7996, d84331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d7997 q = 1) (hb : d84332 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, d84332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7997, d84332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d7998 q = 1) (hb : d84333 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, d84333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d7998, d84333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14234 (p : Pattern) (ha : d84323 p = 1) (hb : d99061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1879 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
  have h2 (q : Pattern) (ha : d1880 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1881 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7080 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7080, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7080, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84322 q = 1) (hb : d99060 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84322, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84322, d99060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84323 q = 1) (hb : d99061 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84323, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84323, d99061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14235 (p : Pattern) (ha : d84329 p = 1) (hb : d99067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7985 q = 1) (hb : d84320 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7985, d84320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10092 q ha hb
    | true =>
      simp only [d7985, d84320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d7986 q = 1) (hb : d84321 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7986, d84321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7986, d84321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84324 q = 1) (hb : d99062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14234 q ha hb
    | true =>
      simp only [d84324, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84325 q = 1) (hb : d99063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84326 q = 1) (hb : d99064 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84326, d99064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84326, d99064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84327 q = 1) (hb : d99065 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84327, d99065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84327, d99065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84328 q = 1) (hb : d99066 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84328, d99066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84328, d99066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84329 q = 1) (hb : d99067 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84329, d99067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84329, d99067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro14236 (p : Pattern) (ha : d84346 p = 1) (hb : d99073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84334 q = 1) (hb : d99068 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84334, d99068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14235 q ha hb
    | true =>
      simp only [d84334, d99068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14233 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84335 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84336 q = 1) (hb : d99069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84336, d99069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84336, d99069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8014 q = 1) (hb : d84341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8014, d84341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10091 q ha hb
    | true =>
      simp only [d8014, d84341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8015 q = 1) (hb : d84342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8015, d84342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8015, d84342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d84343 q = 1) (hb : d99070 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84343, d99070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84343, d99070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84344 q = 1) (hb : d99071 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84344, d99071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84344, d99071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84345 q = 1) (hb : d99072 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84345, d99072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84345, d99072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84346 q = 1) (hb : d99073 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84346, d99073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84346, d99073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro14237 (p : Pattern) (ha : d84352 p = 1) (hb : d99079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7895 q = 1) (hb : d84241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, d84241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7895, d84241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14219 q ha hb
  have h2 (q : Pattern) (ha : d7896 q = 1) (hb : d84242 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, d84242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7896, d84242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7904 q = 1) (hb : d84250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d84250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14219 q ha hb
    | true =>
      simp only [d7904, d84250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14221 q ha hb
  have h4 (q : Pattern) (ha : d7905 q = 1) (hb : d84251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d84251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7905, d84251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7906 q = 1) (hb : d84252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, d84252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7906, d84252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84304 q = 1) (hb : d99048 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84304, d99048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14227 q ha hb
    | true =>
      simp only [d84304, d99048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14231 q ha hb
  have h7 (q : Pattern) (ha : d7971 q = 1) (hb : d84306 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, d84306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14222 q ha hb
    | true =>
      simp only [d7971, d84306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q ha hb
  have h8 (q : Pattern) (ha : d84307 q = 1) (hb : d99049 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84307, d99049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84307, d99049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d84308 q = 1) (hb : d99050 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84308, d99050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84308, d99050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84309 q = 1) (hb : d99051 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84309, d99051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84309, d99051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84313 q = 1) (hb : d99055 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84313, d99055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84313, d99055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14232 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro224 q ha hb
  have h13 (q : Pattern) (ha : d84314 q = 1) (hb : d99056 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84314, d99056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84314, d99056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84315 q = 1) (hb : d99057 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84315, d99057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84315, d99057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84316 q = 1) (hb : d99058 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84316, d99058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84316, d99058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84317 q = 1) (hb : d99059 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84317, d99059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84317, d99059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84347 q = 1) (hb : d99074 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84347, d99074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84347, d99074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14236 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro229 q ha hb
  have h19 (q : Pattern) (ha : d84348 q = 1) (hb : d99075 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84348, d99075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84348, d99075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84349 q = 1) (hb : d99076 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84349, d99076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84349, d99076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84350 q = 1) (hb : d99077 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84350, d99077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84350, d99077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84351 q = 1) (hb : d99078 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84351, d99078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84351, d99078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84352 q = 1) (hb : d99079 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84352, d99079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84352, d99079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro14238 (p : Pattern) (ha : d84358 p = 1) (hb : d99085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84353 q = 1) (hb : d99080 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84353, d99080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84353, d99080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14237 q ha hb
  have h2 (q : Pattern) (ha : d84354 q = 1) (hb : d99081 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84354, d99081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84354, d99081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84355 q = 1) (hb : d99082 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84355, d99082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84355, d99082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84356 q = 1) (hb : d99083 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84356, d99083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84356, d99083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84357 q = 1) (hb : d99084 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84357, d99084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84357, d99084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84358 q = 1) (hb : d99085 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84358, d99085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84358, d99085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14239 (p : Pattern) (ha : d8043 p = 1) (hb : d84370 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d84365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10097 q ha hb
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d84366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d84367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d84368 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8042 q = 1) (hb : d84369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d84369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8042, d84369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8043 q = 1) (hb : d84370 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, d84370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8043, d84370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14240 (p : Pattern) (ha : d8049 p = 1) (hb : d84376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14239 q ha hb
    | true =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d84372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d84373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d84374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d84375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8049 q = 1) (hb : d84376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d84376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d84376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro14241 (p : Pattern) (ha : d8052 p = 1) (hb : d84379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d84365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10097 q ha hb
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d84366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d84367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d84368 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8042 q = 1) (hb : d84369 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d84369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8042, d84369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8052 q = 1) (hb : d84379 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, d84379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8052, d84379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro14242 (p : Pattern) (ha : d8058 p = 1) (hb : d84385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14239 q ha hb
    | true =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d84372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d84373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d84374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d84375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8053 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d84380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14241 q ha hb
    | true =>
      simp only [d8053, d84380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q ha hb
  have h7 (q : Pattern) (ha : d8054 q = 1) (hb : d84381 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d84381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d84381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8055 q = 1) (hb : d84382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d84382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8055, d84382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8056 q = 1) (hb : d84383 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d84383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d84383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8057 q = 1) (hb : d84384 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d84384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d84384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8058 q = 1) (hb : d84385 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d84385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8058, d84385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14243 (p : Pattern) (ha : d8125 p = 1) (hb : d84441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8044 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14239 q ha hb
    | true =>
      simp only [d8044, d84371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
  have h2 (q : Pattern) (ha : d8045 q = 1) (hb : d84372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d84372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8046 q = 1) (hb : d84373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8046, d84373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8047 q = 1) (hb : d84374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d84374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8048 q = 1) (hb : d84375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d84375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8125 q = 1) (hb : d84441 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, d84441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8125, d84441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro14244 (p : Pattern) (ha : d8063 p = 1) (hb : d84390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d84365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10097 q ha hb
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d84366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d84367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d84368 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8062 q = 1) (hb : d84389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d84389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d84389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8063 q = 1) (hb : d84390 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, d84390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8063, d84390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14245 (p : Pattern) (ha : d8070 p = 1) (hb : d84397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d84365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10097 q ha hb
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d84366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d84367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8068 q = 1) (hb : d84395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d84395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d84395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8069 q = 1) (hb : d84396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d84396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8069, d84396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8070 q = 1) (hb : d84397 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, d84397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8070, d84397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14246 (p : Pattern) (ha : d84364 p = 1) (hb : d99091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2073 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
  have h2 (q : Pattern) (ha : d2074 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2075 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7115 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d7115, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7115, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84363 q = 1) (hb : d99090 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84363, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84363, d99090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84364 q = 1) (hb : d99091 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84364, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84364, d99091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro14247 (p : Pattern) (ha : d84408 p = 1) (hb : d99097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8076 q = 1) (hb : d84403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8076, d84403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10105 q ha hb
    | true =>
      simp only [d8076, d84403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8077 q = 1) (hb : d84404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8077, d84404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8077, d84404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84405 q = 1) (hb : d99094 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84405, d99094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84405, d99094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84406 q = 1) (hb : d99095 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84406, d99095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84406, d99095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84407 q = 1) (hb : d99096 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84407, d99096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84407, d99096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84408 q = 1) (hb : d99097 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84408, d99097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84408, d99097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro14248 (p : Pattern) (ha : d84420 p = 1) (hb : d99103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8064 q = 1) (hb : d84391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d84391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14244 q ha hb
    | true =>
      simp only [d8064, d84391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q ha hb
  have h2 (q : Pattern) (ha : d8065 q = 1) (hb : d84392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d84392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d84392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8066 q = 1) (hb : d84393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d84393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8066, d84393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8067 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d84394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d84394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8071 q = 1) (hb : d84398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d84398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14245 q ha hb
    | true =>
      simp only [d8071, d84398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h6 (q : Pattern) (ha : d8072 q = 1) (hb : d84399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d84399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d84399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8073 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d84400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8073, d84400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d84409 q = 1) (hb : d99098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84409, d99098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14247 q ha hb
    | true =>
      simp only [d84409, d99098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14239 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84410 q = 1) (hb : d99099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d99099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84410, d99099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d8097 q = 1) (hb : d84415 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d84415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10102 q ha hb
    | true =>
      simp only [d8097, d84415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d8098 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, d84416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d8098, d84416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d84417 q = 1) (hb : d99100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d99100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84417, d99100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84418 q = 1) (hb : d99101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d99101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d84418, d99101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84419 q = 1) (hb : d99102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d99102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84419, d99102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84420 q = 1) (hb : d99103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84420, d99103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84420, d99103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro14249 (p : Pattern) (ha : d8103 p = 1) (hb : d84421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8038 q = 1) (hb : d84365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10097 q ha hb
    | true =>
      simp only [d8038, d84365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d84366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d84366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8040 q = 1) (hb : d84367 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8040, d84367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8041 q = 1) (hb : d84368 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8041, d84368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8062 q = 1) (hb : d84389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d84389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d84389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8103 q = 1) (hb : d84421 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, d84421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8103, d84421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
