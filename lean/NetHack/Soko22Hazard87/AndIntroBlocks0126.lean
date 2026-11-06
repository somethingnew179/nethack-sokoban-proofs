import NetHack.Soko22Hazard87.AndIntroBlocks0125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro31500 (p : Pattern) (ha : d12693 p = 1) (hb : d159762 p = 1) : d160117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12688 q = 1) (hb : d159762 q = 1) : d160108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d160108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31474 q ha hb
    | true =>
      simp only [d12688, d160108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31499 q ha hb
  have h2 (q : Pattern) (ha : d12689 q = 1) (hb : d159762 q = 1) : d160109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d160109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d160109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12690 q = 1) (hb : d159762 q = 1) : d160110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d160110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d160110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4914 q = 1) (hb : d159762 q = 1) : d160111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31499 q ha hb
    | true =>
      simp only [d4914, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31498 q ha hb
  have h5 (q : Pattern) (ha : d4915 q = 1) (hb : d159762 q = 1) : d160112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4916 q = 1) (hb : d159762 q = 1) : d160113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12691 q = 1) (hb : d159762 q = 1) : d160114 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d160114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12691, d160114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4917 q = 1) (hb : d159762 q = 1) : d160115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4917, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12692 q = 1) (hb : d159762 q = 1) : d160116 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d160116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12692, d160116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12693 q = 1) (hb : d159762 q = 1) : d160117 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d160117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12693, d160117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31501 (p : Pattern) (ha : d12697 p = 1) (hb : d159762 p = 1) : d160121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4914 q = 1) (hb : d159762 q = 1) : d160111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31499 q ha hb
    | true =>
      simp only [d4914, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31498 q ha hb
  have h2 (q : Pattern) (ha : d4915 q = 1) (hb : d159762 q = 1) : d160112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4916 q = 1) (hb : d159762 q = 1) : d160113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4917 q = 1) (hb : d159762 q = 1) : d160115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4917, d160115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12696 q = 1) (hb : d159762 q = 1) : d160120 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12696, d160120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12696, d160120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12697 q = 1) (hb : d159762 q = 1) : d160121 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12697, d160121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12697, d160121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31502 (p : Pattern) (ha : d12703 p = 1) (hb : d159762 p = 1) : d160127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d159762 q = 1) : d160124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d159762 q = 1) : d160125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d160125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d160125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d159762 q = 1) : d160126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d160126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d160126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12703 q = 1) (hb : d159762 q = 1) : d160127 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d160127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d160127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31503 (p : Pattern) (ha : d12707 p = 1) (hb : d159762 p = 1) : d160131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d159762 q = 1) : d160129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d159762 q = 1) : d160130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12707 q = 1) (hb : d159762 q = 1) : d160131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12707, d160131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12707, d160131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31504 (p : Pattern) (ha : d12713 p = 1) (hb : d159762 p = 1) : d160137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d159762 q = 1) : d160132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d160132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31502 q ha hb
    | true =>
      simp only [d12708, d160132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31503 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d159762 q = 1) : d160133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d160133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d160133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d159762 q = 1) : d160134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d160134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d160134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d159762 q = 1) : d160135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d160135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d160135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d159762 q = 1) : d160136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d160136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d160136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12713 q = 1) (hb : d159762 q = 1) : d160137 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d160137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d160137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31505 (p : Pattern) (ha : d12716 p = 1) (hb : d159762 p = 1) : d160140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d159762 q = 1) : d160124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d159762 q = 1) : d160125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d160125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d160125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12702 q = 1) (hb : d159762 q = 1) : d160126 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d160126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12702, d160126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12716 q = 1) (hb : d159762 q = 1) : d160140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d160140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12716, d160140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31506 (p : Pattern) (ha : d12717 p = 1) (hb : d159762 p = 1) : d160141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d159762 q = 1) : d160129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d159762 q = 1) : d160130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d160130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12717 q = 1) (hb : d159762 q = 1) : d160141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12717, d160141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12717, d160141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31507 (p : Pattern) (ha : d12723 p = 1) (hb : d159762 p = 1) : d160147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d159762 q = 1) : d160132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d160132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31502 q ha hb
    | true =>
      simp only [d12708, d160132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31503 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d159762 q = 1) : d160133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d160133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d160133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d159762 q = 1) : d160134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d160134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d160134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d159762 q = 1) : d160135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d160135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d160135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d159762 q = 1) : d160136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d160136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d160136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12718 q = 1) (hb : d159762 q = 1) : d160142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d160142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31505 q ha hb
    | true =>
      simp only [d12718, d160142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31506 q ha hb
  have h7 (q : Pattern) (ha : d12719 q = 1) (hb : d159762 q = 1) : d160143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d160143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d160143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12720 q = 1) (hb : d159762 q = 1) : d160144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d160144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12720, d160144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12721 q = 1) (hb : d159762 q = 1) : d160145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d160145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d160145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12722 q = 1) (hb : d159762 q = 1) : d160146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d160146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d160146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12723 q = 1) (hb : d159762 q = 1) : d160147 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d160147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12723, d160147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31508 (p : Pattern) (ha : d12833 p = 1) (hb : d159762 p = 1) : d160221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12708 q = 1) (hb : d159762 q = 1) : d160132 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d160132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31502 q ha hb
    | true =>
      simp only [d12708, d160132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31503 q ha hb
  have h2 (q : Pattern) (ha : d12709 q = 1) (hb : d159762 q = 1) : d160133 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d160133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d160133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12710 q = 1) (hb : d159762 q = 1) : d160134 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d160134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12710, d160134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12711 q = 1) (hb : d159762 q = 1) : d160135 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d160135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d160135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12712 q = 1) (hb : d159762 q = 1) : d160136 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d160136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d160136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12828 q = 1) (hb : d159762 q = 1) : d160216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31503 q ha hb
    | true =>
      simp only [d12828, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12829 q = 1) (hb : d159762 q = 1) : d160217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12830 q = 1) (hb : d159762 q = 1) : d160218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12830, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12831 q = 1) (hb : d159762 q = 1) : d160219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12832 q = 1) (hb : d159762 q = 1) : d160220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12833 q = 1) (hb : d159762 q = 1) : d160221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d160221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12833, d160221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31509 (p : Pattern) (ha : d12839 p = 1) (hb : d159762 p = 1) : d160227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12828 q = 1) (hb : d159762 q = 1) : d160216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31503 q ha hb
    | true =>
      simp only [d12828, d160216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12829 q = 1) (hb : d159762 q = 1) : d160217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d160217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12830 q = 1) (hb : d159762 q = 1) : d160218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12830, d160218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12831 q = 1) (hb : d159762 q = 1) : d160219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d160219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12832 q = 1) (hb : d159762 q = 1) : d160220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d160220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12834 q = 1) (hb : d159762 q = 1) : d160222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31506 q ha hb
    | true =>
      simp only [d12834, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12835 q = 1) (hb : d159762 q = 1) : d160223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12836 q = 1) (hb : d159762 q = 1) : d160224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12836, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12837 q = 1) (hb : d159762 q = 1) : d160225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12838 q = 1) (hb : d159762 q = 1) : d160226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12839 q = 1) (hb : d159762 q = 1) : d160227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12839, d160227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12839, d160227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31510 (p : Pattern) (ha : d12848 p = 1) (hb : d159762 p = 1) : d160236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12834 q = 1) (hb : d159762 q = 1) : d160222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31506 q ha hb
    | true =>
      simp only [d12834, d160222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12835 q = 1) (hb : d159762 q = 1) : d160223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d160223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12836 q = 1) (hb : d159762 q = 1) : d160224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12836, d160224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12837 q = 1) (hb : d159762 q = 1) : d160225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d160225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12838 q = 1) (hb : d159762 q = 1) : d160226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d160226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12848 q = 1) (hb : d159762 q = 1) : d160236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12848, d160236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12848, d160236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31511 (p : Pattern) (ha : d986 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d980 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d980, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d986, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31512 (p : Pattern) (ha : d6210 p = 1) (hb : d159762 p = 1) : d160248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d415 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d974 q = 1) (hb : d100904 q = 1) : d974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d975 q = 1) (hb : d159761 q = 1) : d160247 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d159761, d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d975, d159761, d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6210 q = 1) (hb : d159762 q = 1) : d160248 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, d159762, d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6210, d159762, d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31513 (p : Pattern) (ha : d12885 p = 1) (hb : d159762 p = 1) : d160271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6211 q = 1) (hb : d159762 q = 1) : d160253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31512 q ha hb
    | true =>
      simp only [d6211, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31511 q ha hb
  have h2 (q : Pattern) (ha : d6212 q = 1) (hb : d159762 q = 1) : d160254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6213 q = 1) (hb : d159762 q = 1) : d160255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6214 q = 1) (hb : d159762 q = 1) : d160261 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6214, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12884 q = 1) (hb : d159762 q = 1) : d160270 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12884, d160270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12884, d160270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12885 q = 1) (hb : d159762 q = 1) : d160271 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12885, d160271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12885, d160271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31514 (p : Pattern) (ha : d12935 p = 1) (hb : d159762 p = 1) : d160294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12886 q = 1) (hb : d159762 q = 1) : d160272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31513 q ha hb
    | true =>
      simp only [d12886, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12887 q = 1) (hb : d159762 q = 1) : d160273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12932 q = 1) (hb : d159762 q = 1) : d160291 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12932, d160291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12932, d160291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12933 q = 1) (hb : d159762 q = 1) : d160292 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12933, d160292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12933, d160292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12934 q = 1) (hb : d159762 q = 1) : d160293 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12934, d160293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12934, d160293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12935 q = 1) (hb : d159762 q = 1) : d160294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12935, d160294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12935, d160294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31515 (p : Pattern) (ha : d12941 p = 1) (hb : d159762 p = 1) : d160300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12936 q = 1) (hb : d159762 q = 1) : d160295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12936, d160295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31514 q ha hb
    | true =>
      simp only [d12936, d160295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12937 q = 1) (hb : d159762 q = 1) : d160296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12937, d160296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12937, d160296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12938 q = 1) (hb : d159762 q = 1) : d160297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12938, d160297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12938, d160297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12939 q = 1) (hb : d159762 q = 1) : d160298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12939, d160298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12939, d160298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12940 q = 1) (hb : d159762 q = 1) : d160299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12940, d160299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12940, d160299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12941 q = 1) (hb : d159762 q = 1) : d160300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12941, d160300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12941, d160300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31516 (p : Pattern) (ha : d12728 p = 1) (hb : d159762 p = 1) : d160152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d159762 q = 1) : d160124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d159762 q = 1) : d160125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d160125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d160125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d159762 q = 1) : d160151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d160151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d160151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12728 q = 1) (hb : d159762 q = 1) : d160152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d160152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d160152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31517 (p : Pattern) (ha : d12730 p = 1) (hb : d159762 p = 1) : d160154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d159762 q = 1) : d160129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d159762 q = 1) : d160153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12730 q = 1) (hb : d159762 q = 1) : d160154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12730, d160154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12730, d160154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31518 (p : Pattern) (ha : d12737 p = 1) (hb : d159762 p = 1) : d160161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d159762 q = 1) : d160124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d159762 q = 1) : d160159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d160159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d160159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d159762 q = 1) : d160160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d160160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d160160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12737 q = 1) (hb : d159762 q = 1) : d160161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d160161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d160161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31519 (p : Pattern) (ha : d12740 p = 1) (hb : d159762 p = 1) : d160164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d159762 q = 1) : d160162 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d159762 q = 1) : d160163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d159762 q = 1) : d160164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12740, d160164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12740, d160164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31520 (p : Pattern) (ha : d12744 p = 1) (hb : d159762 p = 1) : d160169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d837 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d546 q = 1) (hb : d100904 q = 1) : d546 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d838 q = 1) (hb : d159761 q = 1) : d160168 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d838, d159761, d160168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d838, d159761, d160168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12744 q = 1) (hb : d159762 q = 1) : d160169 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12744, d159762, d160169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12744, d159762, d160169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31521 (p : Pattern) (ha : d12751 p = 1) (hb : d159762 p = 1) : d160107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12749 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d754 q = 1) (hb : d100904 q = 1) : d754 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12750 q = 1) (hb : d159761 q = 1) : d160106 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d159761, d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12750, d159761, d160106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12751 q = 1) (hb : d159762 q = 1) : d160107 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12751, d159762, d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12751, d159762, d160107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31522 (p : Pattern) (ha : d12757 p = 1) (hb : d159762 p = 1) : d160175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12745 q = 1) (hb : d159762 q = 1) : d160170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12745, d160170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31520 q ha hb
    | true =>
      simp only [d12745, d160170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31474 q ha hb
  have h2 (q : Pattern) (ha : d12746 q = 1) (hb : d159762 q = 1) : d160171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12746, d160171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12746, d160171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12747 q = 1) (hb : d159762 q = 1) : d160172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12747, d160172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12747, d160172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12752 q = 1) (hb : d159762 q = 1) : d160108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12752, d160108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31474 q ha hb
    | true =>
      simp only [d12752, d160108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31521 q ha hb
  have h5 (q : Pattern) (ha : d12753 q = 1) (hb : d159762 q = 1) : d160109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12753, d160109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12753, d160109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12754 q = 1) (hb : d159762 q = 1) : d160110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12754, d160110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12754, d160110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12755 q = 1) (hb : d159762 q = 1) : d160173 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d160173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12755, d160173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12688 q = 1) (hb : d159762 q = 1) : d160108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d160108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31474 q ha hb
    | true =>
      simp only [d12688, d160108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31499 q ha hb
  have h9 (q : Pattern) (ha : d12689 q = 1) (hb : d159762 q = 1) : d160109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d160109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12689, d160109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12690 q = 1) (hb : d159762 q = 1) : d160110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d160110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12690, d160110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4914 q = 1) (hb : d159762 q = 1) : d160111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31499 q ha hb
    | true =>
      simp only [d4914, d160111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31498 q ha hb
  have h12 (q : Pattern) (ha : d4915 q = 1) (hb : d159762 q = 1) : d160112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d160112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4916 q = 1) (hb : d159762 q = 1) : d160113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d160113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12691 q = 1) (hb : d159762 q = 1) : d160114 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d160114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12691, d160114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12756 q = 1) (hb : d159762 q = 1) : d160174 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d160174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12756, d160174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12757 q = 1) (hb : d159762 q = 1) : d160175 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d160175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12757, d160175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31523 (p : Pattern) (ha : d12763 p = 1) (hb : d159762 p = 1) : d160181 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d159762 q = 1) : d160176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d160176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31522 q ha hb
    | true =>
      simp only [d12758, d160176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d159762 q = 1) : d160177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d160177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d160177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d159762 q = 1) : d160178 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d160178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d160178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d159762 q = 1) : d160179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d160179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d160179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d159762 q = 1) : d160180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d160180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d160180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d159762 q = 1) : d160181 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d160181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d160181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31524 (p : Pattern) (ha : d12796 p = 1) (hb : d159762 p = 1) : d160187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d159762 q = 1) : d160184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d160184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d160184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d159762 q = 1) : d160185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d160185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d160185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d159762 q = 1) : d160186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d160186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d160186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d159762 q = 1) : d160187 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d160187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d160187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31525 (p : Pattern) (ha : d115359 p = 1) (hb : d159762 p = 1) : d160193 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d159762 q = 1) : d160155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d160155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31516 q ha hb
    | true =>
      simp only [d12731, d160155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31517 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d159762 q = 1) : d160156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d160156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d160156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d159762 q = 1) : d160157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d160157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d160157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d159762 q = 1) : d160158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d160158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d160158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d159762 q = 1) : d160165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d160165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31518 q ha hb
    | true =>
      simp only [d12741, d160165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31519 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d159762 q = 1) : d160166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d160166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d160166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d159762 q = 1) : d160167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d160167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d160167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d159762 q = 1) : d160182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d160182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31523 q ha hb
    | true =>
      simp only [d12764, d160182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31502 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d159762 q = 1) : d160183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d160183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d160183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d159762 q = 1) : d160188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d160188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31524 q ha hb
    | true =>
      simp only [d12797, d160188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d159762 q = 1) : d160189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d160189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d160189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d159762 q = 1) : d160190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d160190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d160190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d159762 q = 1) : d160191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d160191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d160191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d159762 q = 1) : d160192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d160192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d160192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115359 q = 1) (hb : d159762 q = 1) : d160193 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d160193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d160193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31526 (p : Pattern) (ha : d12803 p = 1) (hb : d159762 p = 1) : d160194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d159762 q = 1) : d160124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12701 q = 1) (hb : d159762 q = 1) : d160125 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d160125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12701, d160125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12727 q = 1) (hb : d159762 q = 1) : d160151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d160151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d160151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12803 q = 1) (hb : d159762 q = 1) : d160194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d160194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12803, d160194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31527 (p : Pattern) (ha : d12804 p = 1) (hb : d159762 p = 1) : d160195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d159762 q = 1) : d160129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d160129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12729 q = 1) (hb : d159762 q = 1) : d160153 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12729, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12729, d160153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12804 q = 1) (hb : d159762 q = 1) : d160195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12804, d160195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12804, d160195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31528 (p : Pattern) (ha : d12809 p = 1) (hb : d159762 p = 1) : d160200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12700 q = 1) (hb : d159762 q = 1) : d160124 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d160124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12735 q = 1) (hb : d159762 q = 1) : d160159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d160159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d160159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12736 q = 1) (hb : d159762 q = 1) : d160160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d160160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12736, d160160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12809 q = 1) (hb : d159762 q = 1) : d160200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d160200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12809, d160200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31529 (p : Pattern) (ha : d12810 p = 1) (hb : d159762 p = 1) : d160201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d159762 q = 1) : d160122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31501 q ha hb
    | true =>
      simp only [d12698, d160122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d159762 q = 1) : d160123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d160123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d159762 q = 1) : d160128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d160128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12738 q = 1) (hb : d159762 q = 1) : d160162 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12738, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12738, d160162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12739 q = 1) (hb : d159762 q = 1) : d160163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12739, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12739, d160163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12810 q = 1) (hb : d159762 q = 1) : d160201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12810, d160201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12810, d160201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31530 (p : Pattern) (ha : d12814 p = 1) (hb : d159762 p = 1) : d160205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d159762 q = 1) : d160176 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d160176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31522 q ha hb
    | true =>
      simp only [d12758, d160176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d159762 q = 1) : d160177 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d160177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d160177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d159762 q = 1) : d160178 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d160178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d160178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d159762 q = 1) : d160179 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d160179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d160179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d159762 q = 1) : d160180 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d160180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d160180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d159762 q = 1) : d160205 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d160205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d160205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31531 (p : Pattern) (ha : d12820 p = 1) (hb : d159762 p = 1) : d160208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d159762 q = 1) : d160118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31500 q ha hb
    | true =>
      simp only [d12694, d160118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d159762 q = 1) : d160119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d160119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d159762 q = 1) : d160184 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d160184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d160184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d159762 q = 1) : d160185 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d160185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d160185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d159762 q = 1) : d160186 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d160186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d160186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d159762 q = 1) : d160208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d160208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d160208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31532 (p : Pattern) (ha : d115364 p = 1) (hb : d159762 p = 1) : d160214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12731 q = 1) (hb : d159762 q = 1) : d160155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d160155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31516 q ha hb
    | true =>
      simp only [d12731, d160155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31517 q ha hb
  have h2 (q : Pattern) (ha : d12732 q = 1) (hb : d159762 q = 1) : d160156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d160156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d160156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12733 q = 1) (hb : d159762 q = 1) : d160157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d160157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12733, d160157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12734 q = 1) (hb : d159762 q = 1) : d160158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d160158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d160158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12741 q = 1) (hb : d159762 q = 1) : d160165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d160165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31518 q ha hb
    | true =>
      simp only [d12741, d160165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31519 q ha hb
  have h6 (q : Pattern) (ha : d12742 q = 1) (hb : d159762 q = 1) : d160166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d160166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d160166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12743 q = 1) (hb : d159762 q = 1) : d160167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d160167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12743, d160167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12764 q = 1) (hb : d159762 q = 1) : d160182 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d160182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31523 q ha hb
    | true =>
      simp only [d12764, d160182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31502 q ha hb
  have h9 (q : Pattern) (ha : d115355 q = 1) (hb : d159762 q = 1) : d160183 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d160183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115355, d160183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12797 q = 1) (hb : d159762 q = 1) : d160188 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d160188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31524 q ha hb
    | true =>
      simp only [d12797, d160188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12798 q = 1) (hb : d159762 q = 1) : d160189 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d160189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12798, d160189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115356 q = 1) (hb : d159762 q = 1) : d160190 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d160190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115356, d160190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115357 q = 1) (hb : d159762 q = 1) : d160191 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d160191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115357, d160191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115358 q = 1) (hb : d159762 q = 1) : d160192 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d160192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115358, d160192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12805 q = 1) (hb : d159762 q = 1) : d160196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d160196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31526 q ha hb
    | true =>
      simp only [d12805, d160196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31527 q ha hb
  have h16 (q : Pattern) (ha : d12806 q = 1) (hb : d159762 q = 1) : d160197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d160197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d160197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12807 q = 1) (hb : d159762 q = 1) : d160198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d160198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12807, d160198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12808 q = 1) (hb : d159762 q = 1) : d160199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d160199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d160199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12811 q = 1) (hb : d159762 q = 1) : d160202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d160202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31528 q ha hb
    | true =>
      simp only [d12811, d160202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31529 q ha hb
  have h20 (q : Pattern) (ha : d12812 q = 1) (hb : d159762 q = 1) : d160203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d160203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d160203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d12813 q = 1) (hb : d159762 q = 1) : d160204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d160204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12813, d160204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12815 q = 1) (hb : d159762 q = 1) : d160206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d160206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31530 q ha hb
    | true =>
      simp only [d12815, d160206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31505 q ha hb
  have h23 (q : Pattern) (ha : d115360 q = 1) (hb : d159762 q = 1) : d160207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d160207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115360, d160207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12821 q = 1) (hb : d159762 q = 1) : d160209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d160209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31531 q ha hb
    | true =>
      simp only [d12821, d160209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d12822 q = 1) (hb : d159762 q = 1) : d160210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d160210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12822, d160210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115361 q = 1) (hb : d159762 q = 1) : d160211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d160211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115361, d160211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115362 q = 1) (hb : d159762 q = 1) : d160212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d160212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115362, d160212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115363 q = 1) (hb : d159762 q = 1) : d160213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d160213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115363, d160213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115364 q = 1) (hb : d159762 q = 1) : d160214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d160214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115364, d160214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro31533 (p : Pattern) (ha : d115371 p = 1) (hb : d159762 p = 1) : d160234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d159762 q = 1) : d160206 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d160206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31530 q ha hb
    | true =>
      simp only [d12815, d160206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31505 q ha hb
  have h2 (q : Pattern) (ha : d115360 q = 1) (hb : d159762 q = 1) : d160207 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d160207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115360, d160207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d159762 q = 1) : d160209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d160209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31531 q ha hb
    | true =>
      simp only [d12821, d160209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d159762 q = 1) : d160210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d160210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d160210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d159762 q = 1) : d160211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d160211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d160211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d159762 q = 1) : d160232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d160232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d160232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d159762 q = 1) : d160233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d160233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d160233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d159762 q = 1) : d160234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d160234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d160234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31534 (p : Pattern) (ha : d12854 p = 1) (hb : d159762 p = 1) : d160243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d662 q = 1) (hb : d100904 q = 1) : d662 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d969 q = 1) (hb : d159761 q = 1) : d160242 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d969, d159761, d160242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d969, d159761, d160242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12854 q = 1) (hb : d159762 q = 1) : d160243 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12854, d159762, d160243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12854, d159762, d160243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31535 (p : Pattern) (ha : d12863 p = 1) (hb : d159762 p = 1) : d160248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12861 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d974 q = 1) (hb : d100904 q = 1) : d974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12862 q = 1) (hb : d159761 q = 1) : d160247 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d159761, d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d12862, d159761, d160247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12863 q = 1) (hb : d159762 q = 1) : d160248 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12863, d159762, d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12863, d159762, d160248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31536 (p : Pattern) (ha : d12873 p = 1) (hb : d159762 p = 1) : d160258 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12855 q = 1) (hb : d159762 q = 1) : d160244 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12855, d160244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31534 q ha hb
    | true =>
      simp only [d12855, d160244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31488 q ha hb
  have h2 (q : Pattern) (ha : d12856 q = 1) (hb : d159762 q = 1) : d160245 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12856, d160245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12856, d160245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12857 q = 1) (hb : d159762 q = 1) : d160246 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12857, d160246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12857, d160246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12864 q = 1) (hb : d159762 q = 1) : d160249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12864, d160249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31488 q ha hb
    | true =>
      simp only [d12864, d160249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31535 q ha hb
  have h5 (q : Pattern) (ha : d12865 q = 1) (hb : d159762 q = 1) : d160250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12865, d160250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12865, d160250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12866 q = 1) (hb : d159762 q = 1) : d160251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12866, d160251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12866, d160251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12867 q = 1) (hb : d159762 q = 1) : d160252 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d160252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12867, d160252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12868 q = 1) (hb : d159762 q = 1) : d160249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d160249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31488 q ha hb
    | true =>
      simp only [d12868, d160249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31512 q ha hb
  have h9 (q : Pattern) (ha : d12869 q = 1) (hb : d159762 q = 1) : d160250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d160250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d160250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12870 q = 1) (hb : d159762 q = 1) : d160251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d160251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d160251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6211 q = 1) (hb : d159762 q = 1) : d160253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31512 q ha hb
    | true =>
      simp only [d6211, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31511 q ha hb
  have h12 (q : Pattern) (ha : d6212 q = 1) (hb : d159762 q = 1) : d160254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6213 q = 1) (hb : d159762 q = 1) : d160255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12871 q = 1) (hb : d159762 q = 1) : d160256 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d160256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12871, d160256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d12872 q = 1) (hb : d159762 q = 1) : d160257 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d160257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12872, d160257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d12873 q = 1) (hb : d159762 q = 1) : d160258 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d160258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d12873, d160258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31537 (p : Pattern) (ha : d12877 p = 1) (hb : d159762 p = 1) : d160263 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12868 q = 1) (hb : d159762 q = 1) : d160249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d160249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31488 q ha hb
    | true =>
      simp only [d12868, d160249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31512 q ha hb
  have h2 (q : Pattern) (ha : d12869 q = 1) (hb : d159762 q = 1) : d160250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d160250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12869, d160250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12870 q = 1) (hb : d159762 q = 1) : d160251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d160251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12870, d160251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6211 q = 1) (hb : d159762 q = 1) : d160253 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31512 q ha hb
    | true =>
      simp only [d6211, d160253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31511 q ha hb
  have h5 (q : Pattern) (ha : d6212 q = 1) (hb : d159762 q = 1) : d160254 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6212, d160254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6213 q = 1) (hb : d159762 q = 1) : d160255 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6213, d160255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12871 q = 1) (hb : d159762 q = 1) : d160256 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d160256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12871, d160256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6214 q = 1) (hb : d159762 q = 1) : d160261 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6214, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6214, d160261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12876 q = 1) (hb : d159762 q = 1) : d160262 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d160262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12876, d160262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12877 q = 1) (hb : d159762 q = 1) : d160263 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d160263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12877, d160263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31538 (p : Pattern) (ha : d12883 p = 1) (hb : d159762 p = 1) : d160269 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d159762 q = 1) : d160259 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d160259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31536 q ha hb
    | true =>
      simp only [d12874, d160259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d159762 q = 1) : d160260 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d160260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d160260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d159762 q = 1) : d160264 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d160264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31537 q ha hb
    | true =>
      simp only [d12878, d160264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d159762 q = 1) : d160265 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d160265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d160265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d159762 q = 1) : d160266 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d160266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d160266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d159762 q = 1) : d160267 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d160267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d160267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d159762 q = 1) : d160268 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d160268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d160268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d159762 q = 1) : d160269 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d160269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d160269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31539 (p : Pattern) (ha : d12891 p = 1) (hb : d159762 p = 1) : d160277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d159762 q = 1) : d160264 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d160264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31537 q ha hb
    | true =>
      simp only [d12878, d160264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d159762 q = 1) : d160265 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d160265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d160265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12886 q = 1) (hb : d159762 q = 1) : d160272 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12886, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31513 q ha hb
    | true =>
      simp only [d12886, d160272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12887 q = 1) (hb : d159762 q = 1) : d160273 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12887, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12887, d160273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12888 q = 1) (hb : d159762 q = 1) : d160274 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d160274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d160274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12889 q = 1) (hb : d159762 q = 1) : d160275 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d160275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12889, d160275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12890 q = 1) (hb : d159762 q = 1) : d160276 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d160276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12890, d160276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12891 q = 1) (hb : d159762 q = 1) : d160277 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d160277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12891, d160277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31540 (p : Pattern) (ha : d12924 p = 1) (hb : d159762 p = 1) : d160283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d159762 q = 1) : d160264 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d160264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31537 q ha hb
    | true =>
      simp only [d12878, d160264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d159762 q = 1) : d160265 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d160265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d160265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d159762 q = 1) : d160280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d160280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d160280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d159762 q = 1) : d160281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d160281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d160281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d159762 q = 1) : d160282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d160282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d160282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d159762 q = 1) : d160283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d160283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d160283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31541 (p : Pattern) (ha : d115381 p = 1) (hb : d159762 p = 1) : d160289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d159762 q = 1) : d160278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d160278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31538 q ha hb
    | true =>
      simp only [d12892, d160278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31539 q ha hb
  have h2 (q : Pattern) (ha : d115377 q = 1) (hb : d159762 q = 1) : d160279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d160279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115377, d160279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d159762 q = 1) : d160284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d160284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31540 q ha hb
    | true =>
      simp only [d12925, d160284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d159762 q = 1) : d160285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d160285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d160285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d159762 q = 1) : d160286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d160286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d160286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d159762 q = 1) : d160287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d160287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d160287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d159762 q = 1) : d160288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d160288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d160288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d159762 q = 1) : d160289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d160289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d160289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31542 (p : Pattern) (ha : d115387 p = 1) (hb : d159762 p = 1) : d160306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d159762 q = 1) : d160138 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d160138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d160138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31504 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d159762 q = 1) : d160139 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d160139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d160139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d159762 q = 1) : d160148 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d160148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31504 q ha hb
    | true =>
      simp only [d12724, d160148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31507 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d159762 q = 1) : d160149 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d160149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d160149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d159762 q = 1) : d160150 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d160150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d160150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115365 q = 1) (hb : d159762 q = 1) : d160215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d160215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31525 q ha hb
    | true =>
      simp only [d115365, d160215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31532 q ha hb
  have h7 (q : Pattern) (ha : d12840 q = 1) (hb : d159762 q = 1) : d160228 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d160228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31508 q ha hb
    | true =>
      simp only [d12840, d160228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31509 q ha hb
  have h8 (q : Pattern) (ha : d115366 q = 1) (hb : d159762 q = 1) : d160229 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d160229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d160229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115367 q = 1) (hb : d159762 q = 1) : d160230 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d160230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115367, d160230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115368 q = 1) (hb : d159762 q = 1) : d160231 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d160231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115368, d160231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115372 q = 1) (hb : d159762 q = 1) : d160235 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d160235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115372, d160235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31533 q ha hb
  have h12 (q : Pattern) (ha : d12849 q = 1) (hb : d159762 q = 1) : d160237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12849, d160237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12849, d160237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31510 q ha hb
  have h13 (q : Pattern) (ha : d115373 q = 1) (hb : d159762 q = 1) : d160238 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d160238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115373, d160238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115374 q = 1) (hb : d159762 q = 1) : d160239 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d160239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115374, d160239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115375 q = 1) (hb : d159762 q = 1) : d160240 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d160240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115375, d160240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115376 q = 1) (hb : d159762 q = 1) : d160241 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d160241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115376, d160241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115382 q = 1) (hb : d159762 q = 1) : d160290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d160290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115382, d160290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31541 q ha hb
  have h18 (q : Pattern) (ha : d12942 q = 1) (hb : d159762 q = 1) : d160301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12942, d160301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12942, d160301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31515 q ha hb
  have h19 (q : Pattern) (ha : d115383 q = 1) (hb : d159762 q = 1) : d160302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d160302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115383, d160302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115384 q = 1) (hb : d159762 q = 1) : d160303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d160303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115384, d160303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115385 q = 1) (hb : d159762 q = 1) : d160304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d160304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115385, d160304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115386 q = 1) (hb : d159762 q = 1) : d160305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d160305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115386, d160305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115387 q = 1) (hb : d159762 q = 1) : d160306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d160306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115387, d160306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro31543 (p : Pattern) (ha : d115393 p = 1) (hb : d159762 p = 1) : d160312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d159762 q = 1) : d160307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d160307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d160307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31542 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d159762 q = 1) : d160308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d160308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d160308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d159762 q = 1) : d160309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d160309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d160309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d159762 q = 1) : d160310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d160310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d160310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d159762 q = 1) : d160311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d160311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d160311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d159762 q = 1) : d160312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d160312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d160312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31544 (p : Pattern) (ha : d5009 p = 1) (hb : d159762 p = 1) : d160318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1113 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1124 q = 1) (hb : d100904 q = 1) : d1124 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1125 q = 1) (hb : d159761 q = 1) : d160317 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d159761, d160317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1125, d159761, d160317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5009 q = 1) (hb : d159762 q = 1) : d160318 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5009, d159762, d160318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5009, d159762, d160318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31545 (p : Pattern) (ha : d5023 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5021 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5022 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5022, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5023 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5023, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5023, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31546 (p : Pattern) (ha : d12956 p = 1) (hb : d159762 p = 1) : d160316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1113 q = 1) (hb : d100904 q = 1) : d1113 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1114 q = 1) (hb : d159761 q = 1) : d160315 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d159761, d160315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1114, d159761, d160315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12956 q = 1) (hb : d159762 q = 1) : d160316 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12956, d159762, d160316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12956, d159762, d160316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31547 (p : Pattern) (ha : d12961 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1124 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1127 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1127, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12961 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12961, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31548 (p : Pattern) (ha : d12967 p = 1) (hb : d159762 p = 1) : d160328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d159762 q = 1) : d160319 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d160319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31546 q ha hb
    | true =>
      simp only [d12957, d160319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31544 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d159762 q = 1) : d160320 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d160320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d160320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d159762 q = 1) : d160321 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d160321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d160321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31544 q ha hb
    | true =>
      simp only [d5024, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31545 q ha hb
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12960 q = 1) (hb : d159762 q = 1) : d160325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d160325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d160325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12962 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31544 q ha hb
    | true =>
      simp only [d12962, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31547 q ha hb
  have h9 (q : Pattern) (ha : d12963 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12964 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12965 q = 1) (hb : d159762 q = 1) : d160326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12965, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12966 q = 1) (hb : d159762 q = 1) : d160327 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d160327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12966, d160327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12967 q = 1) (hb : d159762 q = 1) : d160328 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d160328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12967, d160328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro31549 (p : Pattern) (ha : d12971 p = 1) (hb : d159762 p = 1) : d160332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12962 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31544 q ha hb
    | true =>
      simp only [d12962, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31547 q ha hb
  have h2 (q : Pattern) (ha : d12963 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12963, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12964 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12964, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12965 q = 1) (hb : d159762 q = 1) : d160326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12965, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12965, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12970 q = 1) (hb : d159762 q = 1) : d160331 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12970, d160331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12970, d160331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12971 q = 1) (hb : d159762 q = 1) : d160332 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12971, d160332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12971, d160332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31550 (p : Pattern) (ha : d12977 p = 1) (hb : d159762 p = 1) : d160338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31548 q ha hb
    | true =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d159762 q = 1) : d160335 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d159762 q = 1) : d160336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d159762 q = 1) : d160337 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d160337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d160337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12977 q = 1) (hb : d159762 q = 1) : d160338 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d160338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d160338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31551 (p : Pattern) (ha : d12981 p = 1) (hb : d159762 p = 1) : d160342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d159762 q = 1) : d160340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d159762 q = 1) : d160341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d160341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d160341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12981 q = 1) (hb : d159762 q = 1) : d160342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12981, d160342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12981, d160342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31552 (p : Pattern) (ha : d12987 p = 1) (hb : d159762 p = 1) : d160348 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d159762 q = 1) : d160343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d160343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31550 q ha hb
    | true =>
      simp only [d12982, d160343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31551 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d159762 q = 1) : d160344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d160344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d160344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d159762 q = 1) : d160345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d160345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d160345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d159762 q = 1) : d160346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d160346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d160346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d159762 q = 1) : d160347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d160347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d160347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12987 q = 1) (hb : d159762 q = 1) : d160348 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d160348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d160348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31553 (p : Pattern) (ha : d12990 p = 1) (hb : d159762 p = 1) : d160351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31548 q ha hb
    | true =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d159762 q = 1) : d160335 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d159762 q = 1) : d160336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12976 q = 1) (hb : d159762 q = 1) : d160337 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d160337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12976, d160337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12990 q = 1) (hb : d159762 q = 1) : d160351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d160351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12990, d160351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31554 (p : Pattern) (ha : d12991 p = 1) (hb : d159762 p = 1) : d160352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d159762 q = 1) : d160340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12980 q = 1) (hb : d159762 q = 1) : d160341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12980, d160341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12980, d160341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12991 q = 1) (hb : d159762 q = 1) : d160352 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12991, d160352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12991, d160352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31555 (p : Pattern) (ha : d12997 p = 1) (hb : d159762 p = 1) : d160358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12982 q = 1) (hb : d159762 q = 1) : d160343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d160343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31550 q ha hb
    | true =>
      simp only [d12982, d160343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31551 q ha hb
  have h2 (q : Pattern) (ha : d12983 q = 1) (hb : d159762 q = 1) : d160344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d160344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d160344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12984 q = 1) (hb : d159762 q = 1) : d160345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d160345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12984, d160345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12985 q = 1) (hb : d159762 q = 1) : d160346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d160346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d160346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12986 q = 1) (hb : d159762 q = 1) : d160347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d160347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d160347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12992 q = 1) (hb : d159762 q = 1) : d160353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d160353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31553 q ha hb
    | true =>
      simp only [d12992, d160353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31554 q ha hb
  have h7 (q : Pattern) (ha : d12993 q = 1) (hb : d159762 q = 1) : d160354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d160354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d160354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12994 q = 1) (hb : d159762 q = 1) : d160355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d160355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12994, d160355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12995 q = 1) (hb : d159762 q = 1) : d160356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d160356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d160356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12996 q = 1) (hb : d159762 q = 1) : d160357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d160357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d160357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12997 q = 1) (hb : d159762 q = 1) : d160358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d160358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12997, d160358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31556 (p : Pattern) (ha : d13040 p = 1) (hb : d159762 p = 1) : d160328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12957 q = 1) (hb : d159762 q = 1) : d160319 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d160319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31546 q ha hb
    | true =>
      simp only [d12957, d160319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31544 q ha hb
  have h2 (q : Pattern) (ha : d12958 q = 1) (hb : d159762 q = 1) : d160320 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d160320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d160320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d159762 q = 1) : d160321 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d160321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d160321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5024 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31544 q ha hb
    | true =>
      simp only [d5024, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31545 q ha hb
  have h5 (q : Pattern) (ha : d5025 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5026 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12960 q = 1) (hb : d159762 q = 1) : d160325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d160325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d160325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5027 q = 1) (hb : d159762 q = 1) : d160326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5027, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5027, d160326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13039 q = 1) (hb : d159762 q = 1) : d160327 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d160327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13039, d160327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13040 q = 1) (hb : d159762 q = 1) : d160328 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d160328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13040, d160328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31557 (p : Pattern) (ha : d13050 p = 1) (hb : d159762 p = 1) : d160338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31556 q ha hb
    | true =>
      simp only [d13041, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d159762 q = 1) : d160335 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d159762 q = 1) : d160336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d159762 q = 1) : d160337 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d160337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d160337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13050 q = 1) (hb : d159762 q = 1) : d160338 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d160338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d160338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31558 (p : Pattern) (ha : d13134 p = 1) (hb : d159762 p = 1) : d160437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13124 q = 1) (hb : d159762 q = 1) : d160343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d160343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31557 q ha hb
    | true =>
      simp only [d13124, d160343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31551 q ha hb
  have h2 (q : Pattern) (ha : d13125 q = 1) (hb : d159762 q = 1) : d160344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d160344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d160344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13126 q = 1) (hb : d159762 q = 1) : d160345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d160345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13126, d160345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13127 q = 1) (hb : d159762 q = 1) : d160346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d160346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d160346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13128 q = 1) (hb : d159762 q = 1) : d160347 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d160347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d160347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13129 q = 1) (hb : d159762 q = 1) : d160432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d160432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31551 q ha hb
    | true =>
      simp only [d13129, d160432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13130 q = 1) (hb : d159762 q = 1) : d160433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d160433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d160433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13131 q = 1) (hb : d159762 q = 1) : d160434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d160434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13131, d160434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13132 q = 1) (hb : d159762 q = 1) : d160435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d160435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d160435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13133 q = 1) (hb : d159762 q = 1) : d160436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d160436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d160436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13134 q = 1) (hb : d159762 q = 1) : d160437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d160437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13134, d160437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31559 (p : Pattern) (ha : d13140 p = 1) (hb : d159762 p = 1) : d160443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13129 q = 1) (hb : d159762 q = 1) : d160432 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13129, d160432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31551 q ha hb
    | true =>
      simp only [d13129, d160432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13130 q = 1) (hb : d159762 q = 1) : d160433 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13130, d160433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13130, d160433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13131 q = 1) (hb : d159762 q = 1) : d160434 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13131, d160434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13131, d160434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13132 q = 1) (hb : d159762 q = 1) : d160435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13132, d160435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13132, d160435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13133 q = 1) (hb : d159762 q = 1) : d160436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13133, d160436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13133, d160436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13135 q = 1) (hb : d159762 q = 1) : d160438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d160438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31554 q ha hb
    | true =>
      simp only [d13135, d160438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13136 q = 1) (hb : d159762 q = 1) : d160439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d160439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d160439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13137 q = 1) (hb : d159762 q = 1) : d160440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d160440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13137, d160440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13138 q = 1) (hb : d159762 q = 1) : d160441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d160441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d160441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13139 q = 1) (hb : d159762 q = 1) : d160442 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d160442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d160442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13140 q = 1) (hb : d159762 q = 1) : d160443 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13140, d160443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13140, d160443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31560 (p : Pattern) (ha : d13149 p = 1) (hb : d159762 p = 1) : d160452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13135 q = 1) (hb : d159762 q = 1) : d160438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13135, d160438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31554 q ha hb
    | true =>
      simp only [d13135, d160438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13136 q = 1) (hb : d159762 q = 1) : d160439 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13136, d160439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13136, d160439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13137 q = 1) (hb : d159762 q = 1) : d160440 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13137, d160440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13137, d160440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13138 q = 1) (hb : d159762 q = 1) : d160441 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13138, d160441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13138, d160441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13139 q = 1) (hb : d159762 q = 1) : d160442 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13139, d160442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13139, d160442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13149 q = 1) (hb : d159762 q = 1) : d160452 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13149, d160452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13149, d160452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31561 (p : Pattern) (ha : d6349 p = 1) (hb : d159762 p = 1) : d160472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1394 q = 1) (hb : d100904 q = 1) : d1394 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1395 q = 1) (hb : d159761 q = 1) : d160471 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d159761, d160471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1395, d159761, d160471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6349 q = 1) (hb : d159762 q = 1) : d160472 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, d159762, d160472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6349, d159762, d160472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31562 (p : Pattern) (ha : d13190 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1394 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1400 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1400, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13190 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13190, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31563 (p : Pattern) (ha : d13196 p = 1) (hb : d159762 p = 1) : d160494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13191 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31561 q ha hb
    | true =>
      simp only [d13191, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31562 q ha hb
  have h2 (q : Pattern) (ha : d13192 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13193 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13194 q = 1) (hb : d159762 q = 1) : d160484 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13194, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13195 q = 1) (hb : d159762 q = 1) : d160493 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13195, d160493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13195, d160493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13196 q = 1) (hb : d159762 q = 1) : d160494 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13196, d160494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13196, d160494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31564 (p : Pattern) (ha : d13260 p = 1) (hb : d159762 p = 1) : d160517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13197 q = 1) (hb : d159762 q = 1) : d160495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31563 q ha hb
    | true =>
      simp only [d13197, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13198 q = 1) (hb : d159762 q = 1) : d160496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13257 q = 1) (hb : d159762 q = 1) : d160514 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13257, d160514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13257, d160514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13258 q = 1) (hb : d159762 q = 1) : d160515 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13258, d160515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13258, d160515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13259 q = 1) (hb : d159762 q = 1) : d160516 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13259, d160516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13259, d160516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13260 q = 1) (hb : d159762 q = 1) : d160517 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13260, d160517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13260, d160517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31565 (p : Pattern) (ha : d13266 p = 1) (hb : d159762 p = 1) : d160523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13261 q = 1) (hb : d159762 q = 1) : d160518 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13261, d160518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31564 q ha hb
    | true =>
      simp only [d13261, d160518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13262 q = 1) (hb : d159762 q = 1) : d160519 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13262, d160519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13262, d160519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13263 q = 1) (hb : d159762 q = 1) : d160520 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13263, d160520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13263, d160520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13264 q = 1) (hb : d159762 q = 1) : d160521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13264, d160521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13264, d160521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13265 q = 1) (hb : d159762 q = 1) : d160522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13265, d160522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13265, d160522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13266 q = 1) (hb : d159762 q = 1) : d160523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13266, d160523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13266, d160523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31566 (p : Pattern) (ha : d13002 p = 1) (hb : d159762 p = 1) : d160363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31548 q ha hb
    | true =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d159762 q = 1) : d160335 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d159762 q = 1) : d160336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d159762 q = 1) : d160362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d160362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d160362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13002 q = 1) (hb : d159762 q = 1) : d160363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d160363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d160363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31567 (p : Pattern) (ha : d13004 p = 1) (hb : d159762 p = 1) : d160365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d159762 q = 1) : d160340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d159762 q = 1) : d160364 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d160364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d160364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13004 q = 1) (hb : d159762 q = 1) : d160365 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13004, d160365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13004, d160365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31568 (p : Pattern) (ha : d13011 p = 1) (hb : d159762 p = 1) : d160372 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31548 q ha hb
    | true =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d159762 q = 1) : d160335 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d159762 q = 1) : d160370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d160370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d160370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d159762 q = 1) : d160371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d160371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d160371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13011 q = 1) (hb : d159762 q = 1) : d160372 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d160372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d160372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31569 (p : Pattern) (ha : d13014 p = 1) (hb : d159762 p = 1) : d160375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d159762 q = 1) : d160373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d160373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d160373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d159762 q = 1) : d160374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d160374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d160374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d159762 q = 1) : d160375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13014, d160375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13014, d160375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31570 (p : Pattern) (ha : d13018 p = 1) (hb : d159762 p = 1) : d160380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1103 q = 1) (hb : d100904 q = 1) : d1103 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1214 q = 1) (hb : d159761 q = 1) : d160379 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1214, d159761, d160379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1214, d159761, d160379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13018 q = 1) (hb : d159762 q = 1) : d160380 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13018, d159762, d160380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13018, d159762, d160380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31571 (p : Pattern) (ha : d13030 p = 1) (hb : d159762 p = 1) : d160385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13023 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13028 q = 1) (hb : d100904 q = 1) : d13028 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13029 q = 1) (hb : d159761 q = 1) : d160384 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13029, d159761, d160384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13029, d159761, d160384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13030 q = 1) (hb : d159762 q = 1) : d160385 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13030, d159762, d160385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13030, d159762, d160385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31572 (p : Pattern) (ha : d13036 p = 1) (hb : d159762 p = 1) : d160391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13019 q = 1) (hb : d159762 q = 1) : d160381 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13019, d160381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31570 q ha hb
    | true =>
      simp only [d13019, d160381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31546 q ha hb
  have h2 (q : Pattern) (ha : d13020 q = 1) (hb : d159762 q = 1) : d160382 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13020, d160382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13020, d160382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13021 q = 1) (hb : d159762 q = 1) : d160383 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13021, d160383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13021, d160383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13031 q = 1) (hb : d159762 q = 1) : d160386 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13031, d160386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31546 q ha hb
    | true =>
      simp only [d13031, d160386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31571 q ha hb
  have h5 (q : Pattern) (ha : d13032 q = 1) (hb : d159762 q = 1) : d160387 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13032, d160387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13032, d160387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13033 q = 1) (hb : d159762 q = 1) : d160388 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13033, d160388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13033, d160388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13034 q = 1) (hb : d159762 q = 1) : d160389 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d160389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13034, d160389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12957 q = 1) (hb : d159762 q = 1) : d160319 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d160319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31546 q ha hb
    | true =>
      simp only [d12957, d160319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31544 q ha hb
  have h9 (q : Pattern) (ha : d12958 q = 1) (hb : d159762 q = 1) : d160320 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d160320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12958, d160320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12959 q = 1) (hb : d159762 q = 1) : d160321 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d160321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12959, d160321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5024 q = 1) (hb : d159762 q = 1) : d160322 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5024, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31544 q ha hb
    | true =>
      simp only [d5024, d160322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31545 q ha hb
  have h12 (q : Pattern) (ha : d5025 q = 1) (hb : d159762 q = 1) : d160323 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5025, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5025, d160323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5026 q = 1) (hb : d159762 q = 1) : d160324 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5026, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5026, d160324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12960 q = 1) (hb : d159762 q = 1) : d160325 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d160325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d12960, d160325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13035 q = 1) (hb : d159762 q = 1) : d160390 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d160390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13035, d160390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13036 q = 1) (hb : d159762 q = 1) : d160391 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d160391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13036, d160391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31573 (p : Pattern) (ha : d13046 p = 1) (hb : d159762 p = 1) : d160397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d159762 q = 1) : d160392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d160392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31572 q ha hb
    | true =>
      simp only [d13037, d160392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d159762 q = 1) : d160393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d160393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d160393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31556 q ha hb
    | true =>
      simp only [d13041, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d159762 q = 1) : d160394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d160394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d160394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d159762 q = 1) : d160395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d160395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d160395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d159762 q = 1) : d160396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d160396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d160396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d159762 q = 1) : d160397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d160397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d160397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31574 (p : Pattern) (ha : d13091 p = 1) (hb : d159762 p = 1) : d160403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31548 q ha hb
    | true =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d159762 q = 1) : d160400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d160400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d160400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d159762 q = 1) : d160401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d160401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d160401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d159762 q = 1) : d160402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d160402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d160402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d159762 q = 1) : d160403 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d160403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d160403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31575 (p : Pattern) (ha : d115400 p = 1) (hb : d159762 p = 1) : d160409 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d159762 q = 1) : d160366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d160366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31566 q ha hb
    | true =>
      simp only [d13005, d160366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31567 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d159762 q = 1) : d160367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d160367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d160367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d159762 q = 1) : d160368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d160368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d160368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d159762 q = 1) : d160369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d160369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d160369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d159762 q = 1) : d160376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d160376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31568 q ha hb
    | true =>
      simp only [d13015, d160376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31569 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d159762 q = 1) : d160377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d160377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d160377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d159762 q = 1) : d160378 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d160378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d160378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d159762 q = 1) : d160398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d160398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31573 q ha hb
    | true =>
      simp only [d13051, d160398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31557 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d159762 q = 1) : d160399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d160399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d160399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d159762 q = 1) : d160404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d160404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31574 q ha hb
    | true =>
      simp only [d13092, d160404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d159762 q = 1) : d160405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d160405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d160405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d159762 q = 1) : d160406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d160406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d160406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d159762 q = 1) : d160407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d160407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d160407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d159762 q = 1) : d160408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d160408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d160408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115400 q = 1) (hb : d159762 q = 1) : d160409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d160409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d160409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31576 (p : Pattern) (ha : d13098 p = 1) (hb : d159762 p = 1) : d160410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31548 q ha hb
    | true =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d159762 q = 1) : d160335 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12975 q = 1) (hb : d159762 q = 1) : d160336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12975, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13001 q = 1) (hb : d159762 q = 1) : d160362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d160362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d160362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13098 q = 1) (hb : d159762 q = 1) : d160410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d160410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13098, d160410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31577 (p : Pattern) (ha : d13099 p = 1) (hb : d159762 p = 1) : d160411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12979 q = 1) (hb : d159762 q = 1) : d160340 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12979, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12979, d160340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13003 q = 1) (hb : d159762 q = 1) : d160364 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13003, d160364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13003, d160364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13099 q = 1) (hb : d159762 q = 1) : d160411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13099, d160411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13099, d160411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31578 (p : Pattern) (ha : d13104 p = 1) (hb : d159762 p = 1) : d160416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31548 q ha hb
    | true =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12974 q = 1) (hb : d159762 q = 1) : d160335 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13009 q = 1) (hb : d159762 q = 1) : d160370 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d160370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d160370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13010 q = 1) (hb : d159762 q = 1) : d160371 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d160371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13010, d160371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13104 q = 1) (hb : d159762 q = 1) : d160416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d160416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13104, d160416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31579 (p : Pattern) (ha : d13105 p = 1) (hb : d159762 p = 1) : d160417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12978 q = 1) (hb : d159762 q = 1) : d160339 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12978, d160339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13012 q = 1) (hb : d159762 q = 1) : d160373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13012, d160373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13012, d160373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13013 q = 1) (hb : d159762 q = 1) : d160374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13013, d160374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13013, d160374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13105 q = 1) (hb : d159762 q = 1) : d160417 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13105, d160417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13105, d160417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31580 (p : Pattern) (ha : d13109 p = 1) (hb : d159762 p = 1) : d160421 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d159762 q = 1) : d160392 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d160392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31572 q ha hb
    | true =>
      simp only [d13037, d160392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d159762 q = 1) : d160393 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d160393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d160393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31556 q ha hb
    | true =>
      simp only [d13041, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d159762 q = 1) : d160394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d160394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d160394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d159762 q = 1) : d160395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d160395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d160395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d159762 q = 1) : d160396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d160396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d160396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d159762 q = 1) : d160421 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d160421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d160421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31581 (p : Pattern) (ha : d13110 p = 1) (hb : d159762 p = 1) : d160351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31556 q ha hb
    | true =>
      simp only [d13041, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12972 q = 1) (hb : d159762 q = 1) : d160333 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31549 q ha hb
    | true =>
      simp only [d12972, d160333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12973 q = 1) (hb : d159762 q = 1) : d160334 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12973, d160334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13047 q = 1) (hb : d159762 q = 1) : d160335 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d160335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13048 q = 1) (hb : d159762 q = 1) : d160336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13048, d160336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13049 q = 1) (hb : d159762 q = 1) : d160337 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d160337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13049, d160337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13110 q = 1) (hb : d159762 q = 1) : d160351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d160351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13110, d160351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31582 (p : Pattern) (ha : d13116 p = 1) (hb : d159762 p = 1) : d160424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d159762 q = 1) : d160329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31548 q ha hb
    | true =>
      simp only [d12968, d160329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d159762 q = 1) : d160330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d160330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d159762 q = 1) : d160400 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d160400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d160400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d159762 q = 1) : d160401 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d160401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d160401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d159762 q = 1) : d160402 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d160402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d160402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d159762 q = 1) : d160424 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d160424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d160424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31583 (p : Pattern) (ha : d115405 p = 1) (hb : d159762 p = 1) : d160430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13005 q = 1) (hb : d159762 q = 1) : d160366 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d160366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31566 q ha hb
    | true =>
      simp only [d13005, d160366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31567 q ha hb
  have h2 (q : Pattern) (ha : d13006 q = 1) (hb : d159762 q = 1) : d160367 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d160367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d160367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13007 q = 1) (hb : d159762 q = 1) : d160368 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d160368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13007, d160368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13008 q = 1) (hb : d159762 q = 1) : d160369 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d160369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d160369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13015 q = 1) (hb : d159762 q = 1) : d160376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d160376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31568 q ha hb
    | true =>
      simp only [d13015, d160376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31569 q ha hb
  have h6 (q : Pattern) (ha : d13016 q = 1) (hb : d159762 q = 1) : d160377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d160377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d160377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13017 q = 1) (hb : d159762 q = 1) : d160378 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d160378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13017, d160378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13051 q = 1) (hb : d159762 q = 1) : d160398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d160398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31573 q ha hb
    | true =>
      simp only [d13051, d160398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31557 q ha hb
  have h9 (q : Pattern) (ha : d115396 q = 1) (hb : d159762 q = 1) : d160399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d160399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115396, d160399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13092 q = 1) (hb : d159762 q = 1) : d160404 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d160404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31574 q ha hb
    | true =>
      simp only [d13092, d160404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13093 q = 1) (hb : d159762 q = 1) : d160405 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d160405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13093, d160405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115397 q = 1) (hb : d159762 q = 1) : d160406 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d160406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115397, d160406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115398 q = 1) (hb : d159762 q = 1) : d160407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d160407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115398, d160407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115399 q = 1) (hb : d159762 q = 1) : d160408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d160408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115399, d160408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13100 q = 1) (hb : d159762 q = 1) : d160412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d160412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31576 q ha hb
    | true =>
      simp only [d13100, d160412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31577 q ha hb
  have h16 (q : Pattern) (ha : d13101 q = 1) (hb : d159762 q = 1) : d160413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d160413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d160413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13102 q = 1) (hb : d159762 q = 1) : d160414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d160414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13102, d160414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13103 q = 1) (hb : d159762 q = 1) : d160415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d160415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d160415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13106 q = 1) (hb : d159762 q = 1) : d160418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d160418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31578 q ha hb
    | true =>
      simp only [d13106, d160418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31579 q ha hb
  have h20 (q : Pattern) (ha : d13107 q = 1) (hb : d159762 q = 1) : d160419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d160419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d160419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13108 q = 1) (hb : d159762 q = 1) : d160420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d160420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13108, d160420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13111 q = 1) (hb : d159762 q = 1) : d160422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d160422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31580 q ha hb
    | true =>
      simp only [d13111, d160422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31581 q ha hb
  have h23 (q : Pattern) (ha : d115401 q = 1) (hb : d159762 q = 1) : d160423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d160423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115401, d160423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13117 q = 1) (hb : d159762 q = 1) : d160425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d160425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31582 q ha hb
    | true =>
      simp only [d13117, d160425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13118 q = 1) (hb : d159762 q = 1) : d160426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d160426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13118, d160426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115402 q = 1) (hb : d159762 q = 1) : d160427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d160427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115402, d160427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115403 q = 1) (hb : d159762 q = 1) : d160428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d160428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115403, d160428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115404 q = 1) (hb : d159762 q = 1) : d160429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d160429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115404, d160429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115405 q = 1) (hb : d159762 q = 1) : d160430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d160430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115405, d160430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro31584 (p : Pattern) (ha : d115412 p = 1) (hb : d159762 p = 1) : d160450 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d159762 q = 1) : d160422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d160422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31580 q ha hb
    | true =>
      simp only [d13111, d160422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31581 q ha hb
  have h2 (q : Pattern) (ha : d115401 q = 1) (hb : d159762 q = 1) : d160423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d160423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115401, d160423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d159762 q = 1) : d160425 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d160425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31582 q ha hb
    | true =>
      simp only [d13117, d160425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d159762 q = 1) : d160426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d160426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d160426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d159762 q = 1) : d160427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d160427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d160427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d159762 q = 1) : d160448 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d160448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d160448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d159762 q = 1) : d160449 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d160449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d160449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d159762 q = 1) : d160450 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d160450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d160450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31585 (p : Pattern) (ha : d6355 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6353 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6354 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6354, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6354, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6355 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6355, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6355, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31586 (p : Pattern) (ha : d13155 p = 1) (hb : d159762 p = 1) : d160459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1379 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1383 q = 1) (hb : d100904 q = 1) : d1383 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1384 q = 1) (hb : d159761 q = 1) : d160458 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1384, d159761, d160458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1384, d159761, d160458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13155 q = 1) (hb : d159762 q = 1) : d160459 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13155, d159762, d160459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13155, d159762, d160459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31587 (p : Pattern) (ha : d13156 p = 1) (hb : d159762 p = 1) : d160461 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1383 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1388 q = 1) (hb : d100904 q = 1) : d1388 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1389 q = 1) (hb : d159761 q = 1) : d160460 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d159761, d160460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1389, d159761, d160460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13156 q = 1) (hb : d159762 q = 1) : d160461 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13156, d159762, d160461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13156, d159762, d160461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31588 (p : Pattern) (ha : d13169 p = 1) (hb : d159762 p = 1) : d160466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13163 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13167 q = 1) (hb : d100904 q = 1) : d13167 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13168 q = 1) (hb : d159761 q = 1) : d160465 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13168, d159761, d160465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13168, d159761, d160465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13169 q = 1) (hb : d159762 q = 1) : d160466 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13169, d159762, d160466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13169, d159762, d160466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31589 (p : Pattern) (ha : d13179 p = 1) (hb : d159762 p = 1) : d160481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13157 q = 1) (hb : d159762 q = 1) : d160462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13157, d160462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31586 q ha hb
    | true =>
      simp only [d13157, d160462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31587 q ha hb
  have h2 (q : Pattern) (ha : d13158 q = 1) (hb : d159762 q = 1) : d160463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13158, d160463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13158, d160463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13159 q = 1) (hb : d159762 q = 1) : d160464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13159, d160464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13159, d160464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13170 q = 1) (hb : d159762 q = 1) : d160467 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13170, d160467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31587 q ha hb
    | true =>
      simp only [d13170, d160467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31588 q ha hb
  have h5 (q : Pattern) (ha : d13171 q = 1) (hb : d159762 q = 1) : d160468 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13171, d160468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13171, d160468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13172 q = 1) (hb : d159762 q = 1) : d160469 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13172, d160469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13172, d160469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13173 q = 1) (hb : d159762 q = 1) : d160470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d160470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13173, d160470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13174 q = 1) (hb : d159762 q = 1) : d160473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d160473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31587 q ha hb
    | true =>
      simp only [d13174, d160473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31561 q ha hb
  have h9 (q : Pattern) (ha : d13175 q = 1) (hb : d159762 q = 1) : d160474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d160474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d160474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13176 q = 1) (hb : d159762 q = 1) : d160475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d160475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d160475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6356 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31561 q ha hb
    | true =>
      simp only [d6356, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31585 q ha hb
  have h12 (q : Pattern) (ha : d6357 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6358 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13177 q = 1) (hb : d159762 q = 1) : d160479 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d160479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13177, d160479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13178 q = 1) (hb : d159762 q = 1) : d160480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d160480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13178, d160480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13179 q = 1) (hb : d159762 q = 1) : d160481 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d160481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13179, d160481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31590 (p : Pattern) (ha : d13183 p = 1) (hb : d159762 p = 1) : d160486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d159762 q = 1) : d160473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d160473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31587 q ha hb
    | true =>
      simp only [d13174, d160473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31561 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d159762 q = 1) : d160474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d160474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d160474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d159762 q = 1) : d160475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d160475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d160475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31561 q ha hb
    | true =>
      simp only [d6356, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31585 q ha hb
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13177 q = 1) (hb : d159762 q = 1) : d160479 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d160479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d160479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6359 q = 1) (hb : d159762 q = 1) : d160484 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6359, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6359, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13182 q = 1) (hb : d159762 q = 1) : d160485 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d160485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13182, d160485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13183 q = 1) (hb : d159762 q = 1) : d160486 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d160486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13183, d160486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31591 (p : Pattern) (ha : d13189 p = 1) (hb : d159762 p = 1) : d160492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d159762 q = 1) : d160482 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d160482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31589 q ha hb
    | true =>
      simp only [d13180, d160482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d159762 q = 1) : d160483 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d160483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d160483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d159762 q = 1) : d160487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d160487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31590 q ha hb
    | true =>
      simp only [d13184, d160487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d159762 q = 1) : d160488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d160488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d160488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d159762 q = 1) : d160489 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d160489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d160489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d159762 q = 1) : d160490 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d160490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d160490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d159762 q = 1) : d160491 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d160491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d160491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d159762 q = 1) : d160492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d160492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d160492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31592 (p : Pattern) (ha : d13202 p = 1) (hb : d159762 p = 1) : d160500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d159762 q = 1) : d160487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d160487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31590 q ha hb
    | true =>
      simp only [d13184, d160487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d159762 q = 1) : d160488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d160488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d160488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d159762 q = 1) : d160495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31563 q ha hb
    | true =>
      simp only [d13197, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d159762 q = 1) : d160496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13199 q = 1) (hb : d159762 q = 1) : d160497 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d160497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d160497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13200 q = 1) (hb : d159762 q = 1) : d160498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d160498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13200, d160498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13201 q = 1) (hb : d159762 q = 1) : d160499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d160499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13201, d160499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13202 q = 1) (hb : d159762 q = 1) : d160500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d160500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13202, d160500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31593 (p : Pattern) (ha : d13243 p = 1) (hb : d159762 p = 1) : d160486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13174 q = 1) (hb : d159762 q = 1) : d160473 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d160473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31587 q ha hb
    | true =>
      simp only [d13174, d160473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31561 q ha hb
  have h2 (q : Pattern) (ha : d13175 q = 1) (hb : d159762 q = 1) : d160474 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d160474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13175, d160474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d159762 q = 1) : d160475 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d160475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13176, d160475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6356 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6356, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31561 q ha hb
    | true =>
      simp only [d6356, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31585 q ha hb
  have h5 (q : Pattern) (ha : d6357 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6357, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6357, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6358 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6358, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6358, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13177 q = 1) (hb : d159762 q = 1) : d160479 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d160479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d160479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13191 q = 1) (hb : d159762 q = 1) : d160476 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31561 q ha hb
    | true =>
      simp only [d13191, d160476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31562 q ha hb
  have h9 (q : Pattern) (ha : d13192 q = 1) (hb : d159762 q = 1) : d160477 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13192, d160477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13193 q = 1) (hb : d159762 q = 1) : d160478 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13193, d160478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13194 q = 1) (hb : d159762 q = 1) : d160484 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13194, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13194, d160484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13242 q = 1) (hb : d159762 q = 1) : d160485 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d160485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13242, d160485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13243 q = 1) (hb : d159762 q = 1) : d160486 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d160486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13243, d160486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro31594 (p : Pattern) (ha : d13249 p = 1) (hb : d159762 p = 1) : d160506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d159762 q = 1) : d160487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d160487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31593 q ha hb
    | true =>
      simp only [d13244, d160487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d159762 q = 1) : d160488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d160488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d160488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d159762 q = 1) : d160503 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d160503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d160503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d159762 q = 1) : d160504 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d160504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d160504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d159762 q = 1) : d160505 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d160505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d160505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d159762 q = 1) : d160506 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d160506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d160506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31595 (p : Pattern) (ha : d115422 p = 1) (hb : d159762 p = 1) : d160512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d159762 q = 1) : d160501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d160501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31591 q ha hb
    | true =>
      simp only [d13203, d160501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31592 q ha hb
  have h2 (q : Pattern) (ha : d115418 q = 1) (hb : d159762 q = 1) : d160502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d160502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115418, d160502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d159762 q = 1) : d160507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d160507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31594 q ha hb
    | true =>
      simp only [d13250, d160507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d159762 q = 1) : d160508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d160508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d160508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d159762 q = 1) : d160509 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d160509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d160509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d159762 q = 1) : d160510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d160510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d160510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d159762 q = 1) : d160511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d160511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d160511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d159762 q = 1) : d160512 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d160512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d160512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31596 (p : Pattern) (ha : d115428 p = 1) (hb : d159762 p = 1) : d160529 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d159762 q = 1) : d160349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d160349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d160349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31552 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d159762 q = 1) : d160350 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d160350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d160350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d159762 q = 1) : d160359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d160359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31552 q ha hb
    | true =>
      simp only [d12998, d160359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31555 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d159762 q = 1) : d160360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d160360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d160360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d159762 q = 1) : d160361 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d160361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d160361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115406 q = 1) (hb : d159762 q = 1) : d160431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d160431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31575 q ha hb
    | true =>
      simp only [d115406, d160431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31583 q ha hb
  have h7 (q : Pattern) (ha : d13141 q = 1) (hb : d159762 q = 1) : d160444 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d160444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31558 q ha hb
    | true =>
      simp only [d13141, d160444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31559 q ha hb
  have h8 (q : Pattern) (ha : d115407 q = 1) (hb : d159762 q = 1) : d160445 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d160445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d160445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115408 q = 1) (hb : d159762 q = 1) : d160446 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d160446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115408, d160446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115409 q = 1) (hb : d159762 q = 1) : d160447 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d160447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115409, d160447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115413 q = 1) (hb : d159762 q = 1) : d160451 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d160451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115413, d160451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31584 q ha hb
  have h12 (q : Pattern) (ha : d13150 q = 1) (hb : d159762 q = 1) : d160453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13150, d160453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13150, d160453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31560 q ha hb
  have h13 (q : Pattern) (ha : d115414 q = 1) (hb : d159762 q = 1) : d160454 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d160454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115414, d160454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115415 q = 1) (hb : d159762 q = 1) : d160455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d160455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115415, d160455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115416 q = 1) (hb : d159762 q = 1) : d160456 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d160456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115416, d160456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115417 q = 1) (hb : d159762 q = 1) : d160457 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d160457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115417, d160457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115423 q = 1) (hb : d159762 q = 1) : d160513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d160513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115423, d160513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31595 q ha hb
  have h18 (q : Pattern) (ha : d13267 q = 1) (hb : d159762 q = 1) : d160524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13267, d160524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13267, d160524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31565 q ha hb
  have h19 (q : Pattern) (ha : d115424 q = 1) (hb : d159762 q = 1) : d160525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d160525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115424, d160525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115425 q = 1) (hb : d159762 q = 1) : d160526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d160526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115425, d160526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115426 q = 1) (hb : d159762 q = 1) : d160527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d160527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115426, d160527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115427 q = 1) (hb : d159762 q = 1) : d160528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d160528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115427, d160528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115428 q = 1) (hb : d159762 q = 1) : d160529 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d160529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115428, d160529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro31597 (p : Pattern) (ha : d115434 p = 1) (hb : d159762 p = 1) : d160535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d159762 q = 1) : d160530 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d160530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d160530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31596 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d159762 q = 1) : d160531 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d160531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d160531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d159762 q = 1) : d160532 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d160532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d160532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d159762 q = 1) : d160533 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d160533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d160533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d159762 q = 1) : d160534 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d160534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d160534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d159762 q = 1) : d160535 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d160535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d160535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31598 (p : Pattern) (ha : d5120 p = 1) (hb : d159762 p = 1) : d160542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1573 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1585 q = 1) (hb : d100904 q = 1) : d1585 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1586 q = 1) (hb : d159761 q = 1) : d160541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d159761, d160541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1586, d159761, d160541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5120 q = 1) (hb : d159762 q = 1) : d160542 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5120, d159762, d160542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5120, d159762, d160542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31599 (p : Pattern) (ha : d5139 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5137 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5138 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5138, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5139 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5139, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5139, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31600 (p : Pattern) (ha : d13282 p = 1) (hb : d159762 p = 1) : d160540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1558 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1573 q = 1) (hb : d100904 q = 1) : d1573 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1574 q = 1) (hb : d159761 q = 1) : d160539 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d159761, d160539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1574, d159761, d160539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13282 q = 1) (hb : d159762 q = 1) : d160540 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13282, d159762, d160540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13282, d159762, d160540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31601 (p : Pattern) (ha : d13287 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1585 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1588 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1588, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13287 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13287, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31602 (p : Pattern) (ha : d13293 p = 1) (hb : d159762 p = 1) : d160552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d159762 q = 1) : d160543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d160543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31600 q ha hb
    | true =>
      simp only [d13283, d160543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31598 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d159762 q = 1) : d160544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d160544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d160544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d159762 q = 1) : d160545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d160545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d160545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d159762 q = 1) : d160546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31598 q ha hb
    | true =>
      simp only [d5140, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31599 q ha hb
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d159762 q = 1) : d160547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d159762 q = 1) : d160548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13286 q = 1) (hb : d159762 q = 1) : d160549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d160549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d160549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13288 q = 1) (hb : d159762 q = 1) : d160546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31598 q ha hb
    | true =>
      simp only [d13288, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31601 q ha hb
  have h9 (q : Pattern) (ha : d13289 q = 1) (hb : d159762 q = 1) : d160547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13290 q = 1) (hb : d159762 q = 1) : d160548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13291 q = 1) (hb : d159762 q = 1) : d160550 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d160550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13291, d160550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13292 q = 1) (hb : d159762 q = 1) : d160551 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d160551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13292, d160551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13293 q = 1) (hb : d159762 q = 1) : d160552 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d160552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13293, d160552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro31603 (p : Pattern) (ha : d13297 p = 1) (hb : d159762 p = 1) : d160556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13288 q = 1) (hb : d159762 q = 1) : d160546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31598 q ha hb
    | true =>
      simp only [d13288, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31601 q ha hb
  have h2 (q : Pattern) (ha : d13289 q = 1) (hb : d159762 q = 1) : d160547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13289, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13290 q = 1) (hb : d159762 q = 1) : d160548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13290, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13291 q = 1) (hb : d159762 q = 1) : d160550 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13291, d160550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13291, d160550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13296 q = 1) (hb : d159762 q = 1) : d160555 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13296, d160555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13296, d160555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13297 q = 1) (hb : d159762 q = 1) : d160556 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13297, d160556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13297, d160556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31604 (p : Pattern) (ha : d13303 p = 1) (hb : d159762 p = 1) : d160562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31602 q ha hb
    | true =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d159762 q = 1) : d160559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d159762 q = 1) : d160560 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d159762 q = 1) : d160561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d160561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d160561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13303 q = 1) (hb : d159762 q = 1) : d160562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d160562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d160562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31605 (p : Pattern) (ha : d13307 p = 1) (hb : d159762 p = 1) : d160566 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d159762 q = 1) : d160563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d159762 q = 1) : d160564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d160564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d160564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d159762 q = 1) : d160565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d160565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d160565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13307 q = 1) (hb : d159762 q = 1) : d160566 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13307, d160566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13307, d160566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31606 (p : Pattern) (ha : d13313 p = 1) (hb : d159762 p = 1) : d160572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d159762 q = 1) : d160567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d160567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31604 q ha hb
    | true =>
      simp only [d13308, d160567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31605 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d159762 q = 1) : d160568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d160568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d160568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d159762 q = 1) : d160569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d160569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d160569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d159762 q = 1) : d160570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d160570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d160570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d159762 q = 1) : d160571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d160571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d160571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13313 q = 1) (hb : d159762 q = 1) : d160572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d160572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d160572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31607 (p : Pattern) (ha : d13316 p = 1) (hb : d159762 p = 1) : d160575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31602 q ha hb
    | true =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d159762 q = 1) : d160559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d159762 q = 1) : d160560 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13302 q = 1) (hb : d159762 q = 1) : d160561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d160561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13302, d160561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13316 q = 1) (hb : d159762 q = 1) : d160575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d160575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13316, d160575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31608 (p : Pattern) (ha : d13317 p = 1) (hb : d159762 p = 1) : d160576 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d159762 q = 1) : d160563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d159762 q = 1) : d160564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d160564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d160564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13306 q = 1) (hb : d159762 q = 1) : d160565 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13306, d160565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13306, d160565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13317 q = 1) (hb : d159762 q = 1) : d160576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13317, d160576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13317, d160576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31609 (p : Pattern) (ha : d13323 p = 1) (hb : d159762 p = 1) : d160582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13308 q = 1) (hb : d159762 q = 1) : d160567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d160567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31604 q ha hb
    | true =>
      simp only [d13308, d160567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31605 q ha hb
  have h2 (q : Pattern) (ha : d13309 q = 1) (hb : d159762 q = 1) : d160568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d160568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d160568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13310 q = 1) (hb : d159762 q = 1) : d160569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d160569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13310, d160569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13311 q = 1) (hb : d159762 q = 1) : d160570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d160570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d160570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13312 q = 1) (hb : d159762 q = 1) : d160571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d160571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d160571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13318 q = 1) (hb : d159762 q = 1) : d160577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d160577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31607 q ha hb
    | true =>
      simp only [d13318, d160577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31608 q ha hb
  have h7 (q : Pattern) (ha : d13319 q = 1) (hb : d159762 q = 1) : d160578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d160578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d160578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13320 q = 1) (hb : d159762 q = 1) : d160579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d160579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13320, d160579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13321 q = 1) (hb : d159762 q = 1) : d160580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d160580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d160580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13322 q = 1) (hb : d159762 q = 1) : d160581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d160581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d160581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13323 q = 1) (hb : d159762 q = 1) : d160582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d160582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13323, d160582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31610 (p : Pattern) (ha : d13366 p = 1) (hb : d159762 p = 1) : d160552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13283 q = 1) (hb : d159762 q = 1) : d160543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d160543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31600 q ha hb
    | true =>
      simp only [d13283, d160543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31598 q ha hb
  have h2 (q : Pattern) (ha : d13284 q = 1) (hb : d159762 q = 1) : d160544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d160544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d160544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d159762 q = 1) : d160545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d160545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d160545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5140 q = 1) (hb : d159762 q = 1) : d160546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31598 q ha hb
    | true =>
      simp only [d5140, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31599 q ha hb
  have h5 (q : Pattern) (ha : d5141 q = 1) (hb : d159762 q = 1) : d160547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5142 q = 1) (hb : d159762 q = 1) : d160548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13286 q = 1) (hb : d159762 q = 1) : d160549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d160549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d160549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5143 q = 1) (hb : d159762 q = 1) : d160550 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5143, d160550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5143, d160550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13365 q = 1) (hb : d159762 q = 1) : d160551 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d160551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13365, d160551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13366 q = 1) (hb : d159762 q = 1) : d160552 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d160552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13366, d160552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31611 (p : Pattern) (ha : d13376 p = 1) (hb : d159762 p = 1) : d160562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31610 q ha hb
    | true =>
      simp only [d13367, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d159762 q = 1) : d160559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d159762 q = 1) : d160560 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d159762 q = 1) : d160561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d160561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d160561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13376 q = 1) (hb : d159762 q = 1) : d160562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d160562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d160562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31612 (p : Pattern) (ha : d13460 p = 1) (hb : d159762 p = 1) : d160661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13450 q = 1) (hb : d159762 q = 1) : d160567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d160567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31611 q ha hb
    | true =>
      simp only [d13450, d160567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31605 q ha hb
  have h2 (q : Pattern) (ha : d13451 q = 1) (hb : d159762 q = 1) : d160568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d160568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d160568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13452 q = 1) (hb : d159762 q = 1) : d160569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d160569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13452, d160569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13453 q = 1) (hb : d159762 q = 1) : d160570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d160570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d160570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13454 q = 1) (hb : d159762 q = 1) : d160571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d160571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d160571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13455 q = 1) (hb : d159762 q = 1) : d160656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d160656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31605 q ha hb
    | true =>
      simp only [d13455, d160656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13456 q = 1) (hb : d159762 q = 1) : d160657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d160657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d160657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13457 q = 1) (hb : d159762 q = 1) : d160658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d160658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13457, d160658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13458 q = 1) (hb : d159762 q = 1) : d160659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d160659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d160659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13459 q = 1) (hb : d159762 q = 1) : d160660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d160660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d160660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13460 q = 1) (hb : d159762 q = 1) : d160661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d160661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13460, d160661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31613 (p : Pattern) (ha : d13466 p = 1) (hb : d159762 p = 1) : d160667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13455 q = 1) (hb : d159762 q = 1) : d160656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13455, d160656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31605 q ha hb
    | true =>
      simp only [d13455, d160656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13456 q = 1) (hb : d159762 q = 1) : d160657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13456, d160657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13456, d160657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13457 q = 1) (hb : d159762 q = 1) : d160658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13457, d160658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13457, d160658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13458 q = 1) (hb : d159762 q = 1) : d160659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13458, d160659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13458, d160659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13459 q = 1) (hb : d159762 q = 1) : d160660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13459, d160660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13459, d160660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13461 q = 1) (hb : d159762 q = 1) : d160662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d160662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31608 q ha hb
    | true =>
      simp only [d13461, d160662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13462 q = 1) (hb : d159762 q = 1) : d160663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d160663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d160663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13463 q = 1) (hb : d159762 q = 1) : d160664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d160664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13463, d160664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13464 q = 1) (hb : d159762 q = 1) : d160665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d160665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d160665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13465 q = 1) (hb : d159762 q = 1) : d160666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d160666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d160666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13466 q = 1) (hb : d159762 q = 1) : d160667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13466, d160667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13466, d160667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31614 (p : Pattern) (ha : d13475 p = 1) (hb : d159762 p = 1) : d160676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13461 q = 1) (hb : d159762 q = 1) : d160662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13461, d160662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31608 q ha hb
    | true =>
      simp only [d13461, d160662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13462 q = 1) (hb : d159762 q = 1) : d160663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13462, d160663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13462, d160663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13463 q = 1) (hb : d159762 q = 1) : d160664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13463, d160664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13463, d160664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13464 q = 1) (hb : d159762 q = 1) : d160665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13464, d160665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13464, d160665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13465 q = 1) (hb : d159762 q = 1) : d160666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13465, d160666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13465, d160666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13475 q = 1) (hb : d159762 q = 1) : d160676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13475, d160676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13475, d160676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31615 (p : Pattern) (ha : d6495 p = 1) (hb : d159762 p = 1) : d160696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1865 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1871 q = 1) (hb : d100904 q = 1) : d1871 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1872 q = 1) (hb : d159761 q = 1) : d160695 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d159761, d160695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1872, d159761, d160695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6495 q = 1) (hb : d159762 q = 1) : d160696 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, d159762, d160696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6495, d159762, d160696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31616 (p : Pattern) (ha : d13516 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1871 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1877 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1877, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13516 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13516, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31617 (p : Pattern) (ha : d13522 p = 1) (hb : d159762 p = 1) : d160718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13517 q = 1) (hb : d159762 q = 1) : d160700 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31615 q ha hb
    | true =>
      simp only [d13517, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31616 q ha hb
  have h2 (q : Pattern) (ha : d13518 q = 1) (hb : d159762 q = 1) : d160701 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13519 q = 1) (hb : d159762 q = 1) : d160702 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13520 q = 1) (hb : d159762 q = 1) : d160708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d160708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13520, d160708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13521 q = 1) (hb : d159762 q = 1) : d160717 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13521, d160717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13521, d160717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13522 q = 1) (hb : d159762 q = 1) : d160718 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13522, d160718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13522, d160718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31618 (p : Pattern) (ha : d13586 p = 1) (hb : d159762 p = 1) : d160741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13523 q = 1) (hb : d159762 q = 1) : d160719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d160719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31617 q ha hb
    | true =>
      simp only [d13523, d160719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13524 q = 1) (hb : d159762 q = 1) : d160720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d160720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d160720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13583 q = 1) (hb : d159762 q = 1) : d160738 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13583, d160738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13583, d160738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13584 q = 1) (hb : d159762 q = 1) : d160739 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13584, d160739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13584, d160739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13585 q = 1) (hb : d159762 q = 1) : d160740 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13585, d160740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13585, d160740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13586 q = 1) (hb : d159762 q = 1) : d160741 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13586, d160741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13586, d160741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31619 (p : Pattern) (ha : d13592 p = 1) (hb : d159762 p = 1) : d160747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13587 q = 1) (hb : d159762 q = 1) : d160742 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13587, d160742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31618 q ha hb
    | true =>
      simp only [d13587, d160742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13588 q = 1) (hb : d159762 q = 1) : d160743 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13588, d160743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13588, d160743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13589 q = 1) (hb : d159762 q = 1) : d160744 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13589, d160744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13589, d160744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13590 q = 1) (hb : d159762 q = 1) : d160745 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13590, d160745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13590, d160745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13591 q = 1) (hb : d159762 q = 1) : d160746 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13591, d160746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13591, d160746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13592 q = 1) (hb : d159762 q = 1) : d160747 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13592, d160747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13592, d160747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31620 (p : Pattern) (ha : d13328 p = 1) (hb : d159762 p = 1) : d160587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31602 q ha hb
    | true =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d159762 q = 1) : d160559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d159762 q = 1) : d160560 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d159762 q = 1) : d160586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d160586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d160586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13328 q = 1) (hb : d159762 q = 1) : d160587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d160587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d160587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31621 (p : Pattern) (ha : d13330 p = 1) (hb : d159762 p = 1) : d160589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d159762 q = 1) : d160563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d159762 q = 1) : d160564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d160564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d160564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d159762 q = 1) : d160588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d160588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d160588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13330 q = 1) (hb : d159762 q = 1) : d160589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13330, d160589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13330, d160589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31622 (p : Pattern) (ha : d13337 p = 1) (hb : d159762 p = 1) : d160596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31602 q ha hb
    | true =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d159762 q = 1) : d160559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d159762 q = 1) : d160594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d160594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d160594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d159762 q = 1) : d160595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d160595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d160595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13337 q = 1) (hb : d159762 q = 1) : d160596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d160596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d160596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31623 (p : Pattern) (ha : d13340 p = 1) (hb : d159762 p = 1) : d160599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d159762 q = 1) : d160563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d159762 q = 1) : d160597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d160597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d160597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d159762 q = 1) : d160598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d160598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d160598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d159762 q = 1) : d160599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13340, d160599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13340, d160599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31624 (p : Pattern) (ha : d13344 p = 1) (hb : d159762 p = 1) : d160604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1668 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1558 q = 1) (hb : d100904 q = 1) : d1558 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1669 q = 1) (hb : d159761 q = 1) : d160603 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1669, d159761, d160603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1669, d159761, d160603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13344 q = 1) (hb : d159762 q = 1) : d160604 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13344, d159762, d160604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13344, d159762, d160604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31625 (p : Pattern) (ha : d13356 p = 1) (hb : d159762 p = 1) : d160609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13349 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13354 q = 1) (hb : d100904 q = 1) : d13354 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13355 q = 1) (hb : d159761 q = 1) : d160608 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13355, d159761, d160608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13355, d159761, d160608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13356 q = 1) (hb : d159762 q = 1) : d160609 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13356, d159762, d160609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13356, d159762, d160609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31626 (p : Pattern) (ha : d13362 p = 1) (hb : d159762 p = 1) : d160615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13345 q = 1) (hb : d159762 q = 1) : d160605 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13345, d160605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31624 q ha hb
    | true =>
      simp only [d13345, d160605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31600 q ha hb
  have h2 (q : Pattern) (ha : d13346 q = 1) (hb : d159762 q = 1) : d160606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13346, d160606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13346, d160606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13347 q = 1) (hb : d159762 q = 1) : d160607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13347, d160607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13347, d160607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13357 q = 1) (hb : d159762 q = 1) : d160610 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13357, d160610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31600 q ha hb
    | true =>
      simp only [d13357, d160610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31625 q ha hb
  have h5 (q : Pattern) (ha : d13358 q = 1) (hb : d159762 q = 1) : d160611 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13358, d160611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13358, d160611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13359 q = 1) (hb : d159762 q = 1) : d160612 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13359, d160612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13359, d160612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13360 q = 1) (hb : d159762 q = 1) : d160613 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d160613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13360, d160613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13283 q = 1) (hb : d159762 q = 1) : d160543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d160543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31600 q ha hb
    | true =>
      simp only [d13283, d160543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31598 q ha hb
  have h9 (q : Pattern) (ha : d13284 q = 1) (hb : d159762 q = 1) : d160544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d160544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13284, d160544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13285 q = 1) (hb : d159762 q = 1) : d160545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d160545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13285, d160545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5140 q = 1) (hb : d159762 q = 1) : d160546 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5140, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31598 q ha hb
    | true =>
      simp only [d5140, d160546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31599 q ha hb
  have h12 (q : Pattern) (ha : d5141 q = 1) (hb : d159762 q = 1) : d160547 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5141, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5141, d160547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5142 q = 1) (hb : d159762 q = 1) : d160548 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5142, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5142, d160548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13286 q = 1) (hb : d159762 q = 1) : d160549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d160549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13286, d160549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13361 q = 1) (hb : d159762 q = 1) : d160614 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d160614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13361, d160614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13362 q = 1) (hb : d159762 q = 1) : d160615 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d160615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13362, d160615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31627 (p : Pattern) (ha : d13372 p = 1) (hb : d159762 p = 1) : d160621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d159762 q = 1) : d160616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d160616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31626 q ha hb
    | true =>
      simp only [d13363, d160616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d159762 q = 1) : d160617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d160617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d160617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31610 q ha hb
    | true =>
      simp only [d13367, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d159762 q = 1) : d160618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d160618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d160618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d159762 q = 1) : d160619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d160619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d160619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d159762 q = 1) : d160620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d160620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d160620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d159762 q = 1) : d160621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d160621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d160621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31628 (p : Pattern) (ha : d13417 p = 1) (hb : d159762 p = 1) : d160627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31602 q ha hb
    | true =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d159762 q = 1) : d160624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d160624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d160624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d159762 q = 1) : d160625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d160625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d160625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d159762 q = 1) : d160626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d160626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d160626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d159762 q = 1) : d160627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d160627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d160627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31629 (p : Pattern) (ha : d115442 p = 1) (hb : d159762 p = 1) : d160633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d159762 q = 1) : d160590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d160590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31620 q ha hb
    | true =>
      simp only [d13331, d160590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31621 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d159762 q = 1) : d160591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d160591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d160591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d159762 q = 1) : d160592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d160592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d160592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d159762 q = 1) : d160593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d160593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d160593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d159762 q = 1) : d160600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d160600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31622 q ha hb
    | true =>
      simp only [d13341, d160600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31623 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d159762 q = 1) : d160601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d160601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d160601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d159762 q = 1) : d160602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d160602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d160602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d159762 q = 1) : d160622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d160622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31627 q ha hb
    | true =>
      simp only [d13377, d160622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31611 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d159762 q = 1) : d160623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d160623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d160623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d159762 q = 1) : d160628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d160628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31628 q ha hb
    | true =>
      simp only [d13418, d160628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d159762 q = 1) : d160629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d160629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d160629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d159762 q = 1) : d160630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d160630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d160630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d159762 q = 1) : d160631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d160631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d160631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d159762 q = 1) : d160632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d160632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d160632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115442 q = 1) (hb : d159762 q = 1) : d160633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d160633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d160633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31630 (p : Pattern) (ha : d13424 p = 1) (hb : d159762 p = 1) : d160634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31602 q ha hb
    | true =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d159762 q = 1) : d160559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13301 q = 1) (hb : d159762 q = 1) : d160560 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13301, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13327 q = 1) (hb : d159762 q = 1) : d160586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d160586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d160586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13424 q = 1) (hb : d159762 q = 1) : d160634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, d160634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13424, d160634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31631 (p : Pattern) (ha : d13425 p = 1) (hb : d159762 p = 1) : d160635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d159762 q = 1) : d160563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13305 q = 1) (hb : d159762 q = 1) : d160564 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13305, d160564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13305, d160564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13329 q = 1) (hb : d159762 q = 1) : d160588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13329, d160588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13329, d160588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13425 q = 1) (hb : d159762 q = 1) : d160635 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13425, d160635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13425, d160635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31632 (p : Pattern) (ha : d13430 p = 1) (hb : d159762 p = 1) : d160640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31602 q ha hb
    | true =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13300 q = 1) (hb : d159762 q = 1) : d160559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13335 q = 1) (hb : d159762 q = 1) : d160594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d160594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d160594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13336 q = 1) (hb : d159762 q = 1) : d160595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d160595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13336, d160595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13430 q = 1) (hb : d159762 q = 1) : d160640 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13430, d160640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13430, d160640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31633 (p : Pattern) (ha : d13431 p = 1) (hb : d159762 p = 1) : d160641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13304 q = 1) (hb : d159762 q = 1) : d160563 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13304, d160563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13338 q = 1) (hb : d159762 q = 1) : d160597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13338, d160597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13338, d160597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13339 q = 1) (hb : d159762 q = 1) : d160598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13339, d160598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13339, d160598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13431 q = 1) (hb : d159762 q = 1) : d160641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13431, d160641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13431, d160641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31634 (p : Pattern) (ha : d13435 p = 1) (hb : d159762 p = 1) : d160645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d159762 q = 1) : d160616 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d160616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31626 q ha hb
    | true =>
      simp only [d13363, d160616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d159762 q = 1) : d160617 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d160617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d160617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31610 q ha hb
    | true =>
      simp only [d13367, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d159762 q = 1) : d160618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d160618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d160618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d159762 q = 1) : d160619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d160619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d160619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d159762 q = 1) : d160620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d160620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d160620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13435 q = 1) (hb : d159762 q = 1) : d160645 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13435, d160645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13435, d160645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31635 (p : Pattern) (ha : d13436 p = 1) (hb : d159762 p = 1) : d160575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31610 q ha hb
    | true =>
      simp only [d13367, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13298 q = 1) (hb : d159762 q = 1) : d160557 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31603 q ha hb
    | true =>
      simp only [d13298, d160557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13299 q = 1) (hb : d159762 q = 1) : d160558 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13299, d160558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13373 q = 1) (hb : d159762 q = 1) : d160559 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d160559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13374 q = 1) (hb : d159762 q = 1) : d160560 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13374, d160560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13375 q = 1) (hb : d159762 q = 1) : d160561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d160561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13375, d160561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13436 q = 1) (hb : d159762 q = 1) : d160575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13436, d160575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13436, d160575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31636 (p : Pattern) (ha : d13442 p = 1) (hb : d159762 p = 1) : d160648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d159762 q = 1) : d160553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31602 q ha hb
    | true =>
      simp only [d13294, d160553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d159762 q = 1) : d160554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d160554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d159762 q = 1) : d160624 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d160624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d160624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d159762 q = 1) : d160625 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d160625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d160625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d159762 q = 1) : d160626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d160626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d160626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13442 q = 1) (hb : d159762 q = 1) : d160648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13442, d160648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13442, d160648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31637 (p : Pattern) (ha : d115447 p = 1) (hb : d159762 p = 1) : d160654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13331 q = 1) (hb : d159762 q = 1) : d160590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d160590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31620 q ha hb
    | true =>
      simp only [d13331, d160590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31621 q ha hb
  have h2 (q : Pattern) (ha : d13332 q = 1) (hb : d159762 q = 1) : d160591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d160591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d160591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13333 q = 1) (hb : d159762 q = 1) : d160592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d160592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13333, d160592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13334 q = 1) (hb : d159762 q = 1) : d160593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d160593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d160593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13341 q = 1) (hb : d159762 q = 1) : d160600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d160600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31622 q ha hb
    | true =>
      simp only [d13341, d160600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31623 q ha hb
  have h6 (q : Pattern) (ha : d13342 q = 1) (hb : d159762 q = 1) : d160601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d160601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d160601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13343 q = 1) (hb : d159762 q = 1) : d160602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d160602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13343, d160602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13377 q = 1) (hb : d159762 q = 1) : d160622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d160622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31627 q ha hb
    | true =>
      simp only [d13377, d160622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31611 q ha hb
  have h9 (q : Pattern) (ha : d115438 q = 1) (hb : d159762 q = 1) : d160623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d160623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115438, d160623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13418 q = 1) (hb : d159762 q = 1) : d160628 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d160628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31628 q ha hb
    | true =>
      simp only [d13418, d160628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13419 q = 1) (hb : d159762 q = 1) : d160629 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d160629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13419, d160629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115439 q = 1) (hb : d159762 q = 1) : d160630 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d160630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115439, d160630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115440 q = 1) (hb : d159762 q = 1) : d160631 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d160631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115440, d160631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115441 q = 1) (hb : d159762 q = 1) : d160632 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d160632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115441, d160632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13426 q = 1) (hb : d159762 q = 1) : d160636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13426, d160636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31630 q ha hb
    | true =>
      simp only [d13426, d160636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31631 q ha hb
  have h16 (q : Pattern) (ha : d13427 q = 1) (hb : d159762 q = 1) : d160637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13427, d160637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13427, d160637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13428 q = 1) (hb : d159762 q = 1) : d160638 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13428, d160638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13428, d160638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13429 q = 1) (hb : d159762 q = 1) : d160639 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13429, d160639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13429, d160639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13432 q = 1) (hb : d159762 q = 1) : d160642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13432, d160642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31632 q ha hb
    | true =>
      simp only [d13432, d160642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31633 q ha hb
  have h20 (q : Pattern) (ha : d13433 q = 1) (hb : d159762 q = 1) : d160643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13433, d160643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13433, d160643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13434 q = 1) (hb : d159762 q = 1) : d160644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13434, d160644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13434, d160644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13437 q = 1) (hb : d159762 q = 1) : d160646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d160646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31634 q ha hb
    | true =>
      simp only [d13437, d160646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31635 q ha hb
  have h23 (q : Pattern) (ha : d115443 q = 1) (hb : d159762 q = 1) : d160647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d160647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115443, d160647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13443 q = 1) (hb : d159762 q = 1) : d160649 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d160649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31636 q ha hb
    | true =>
      simp only [d13443, d160649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13444 q = 1) (hb : d159762 q = 1) : d160650 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d160650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13444, d160650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115444 q = 1) (hb : d159762 q = 1) : d160651 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d160651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115444, d160651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115445 q = 1) (hb : d159762 q = 1) : d160652 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d160652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115445, d160652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115446 q = 1) (hb : d159762 q = 1) : d160653 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d160653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115446, d160653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115447 q = 1) (hb : d159762 q = 1) : d160654 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d160654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115447, d160654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro31638 (p : Pattern) (ha : d115454 p = 1) (hb : d159762 p = 1) : d160674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13437 q = 1) (hb : d159762 q = 1) : d160646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d160646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31634 q ha hb
    | true =>
      simp only [d13437, d160646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31635 q ha hb
  have h2 (q : Pattern) (ha : d115443 q = 1) (hb : d159762 q = 1) : d160647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d160647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115443, d160647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13443 q = 1) (hb : d159762 q = 1) : d160649 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d160649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31636 q ha hb
    | true =>
      simp only [d13443, d160649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13444 q = 1) (hb : d159762 q = 1) : d160650 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d160650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13444, d160650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115444 q = 1) (hb : d159762 q = 1) : d160651 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d160651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115444, d160651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115452 q = 1) (hb : d159762 q = 1) : d160672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d160672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115452, d160672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115453 q = 1) (hb : d159762 q = 1) : d160673 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d160673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115453, d160673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115454 q = 1) (hb : d159762 q = 1) : d160674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d160674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115454, d160674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31639 (p : Pattern) (ha : d6501 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6500 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6500, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6501 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6501, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6501, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31640 (p : Pattern) (ha : d13481 p = 1) (hb : d159762 p = 1) : d160683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1856 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1860 q = 1) (hb : d100904 q = 1) : d1860 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1861 q = 1) (hb : d159761 q = 1) : d160682 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1861, d159761, d160682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1861, d159761, d160682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13481 q = 1) (hb : d159762 q = 1) : d160683 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13481, d159762, d160683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13481, d159762, d160683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31641 (p : Pattern) (ha : d13482 p = 1) (hb : d159762 p = 1) : d160685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1860 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1865 q = 1) (hb : d100904 q = 1) : d1865 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1866 q = 1) (hb : d159761 q = 1) : d160684 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d159761, d160684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1866, d159761, d160684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13482 q = 1) (hb : d159762 q = 1) : d160685 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13482, d159762, d160685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13482, d159762, d160685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31642 (p : Pattern) (ha : d13495 p = 1) (hb : d159762 p = 1) : d160690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13489 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13493 q = 1) (hb : d100904 q = 1) : d13493 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13494 q = 1) (hb : d159761 q = 1) : d160689 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13494, d159761, d160689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13494, d159761, d160689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13495 q = 1) (hb : d159762 q = 1) : d160690 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13495, d159762, d160690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13495, d159762, d160690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31643 (p : Pattern) (ha : d13505 p = 1) (hb : d159762 p = 1) : d160705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13483 q = 1) (hb : d159762 q = 1) : d160686 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13483, d160686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31640 q ha hb
    | true =>
      simp only [d13483, d160686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31641 q ha hb
  have h2 (q : Pattern) (ha : d13484 q = 1) (hb : d159762 q = 1) : d160687 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13484, d160687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13484, d160687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13485 q = 1) (hb : d159762 q = 1) : d160688 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13485, d160688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13485, d160688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13496 q = 1) (hb : d159762 q = 1) : d160691 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13496, d160691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31641 q ha hb
    | true =>
      simp only [d13496, d160691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31642 q ha hb
  have h5 (q : Pattern) (ha : d13497 q = 1) (hb : d159762 q = 1) : d160692 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13497, d160692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13497, d160692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13498 q = 1) (hb : d159762 q = 1) : d160693 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13498, d160693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13498, d160693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13499 q = 1) (hb : d159762 q = 1) : d160694 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13499, d160694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13499, d160694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13500 q = 1) (hb : d159762 q = 1) : d160697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d160697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31641 q ha hb
    | true =>
      simp only [d13500, d160697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31615 q ha hb
  have h9 (q : Pattern) (ha : d13501 q = 1) (hb : d159762 q = 1) : d160698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d160698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d160698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13502 q = 1) (hb : d159762 q = 1) : d160699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d160699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d160699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6502 q = 1) (hb : d159762 q = 1) : d160700 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31615 q ha hb
    | true =>
      simp only [d6502, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31639 q ha hb
  have h12 (q : Pattern) (ha : d6503 q = 1) (hb : d159762 q = 1) : d160701 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6504 q = 1) (hb : d159762 q = 1) : d160702 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13503 q = 1) (hb : d159762 q = 1) : d160703 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d160703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13503, d160703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13504 q = 1) (hb : d159762 q = 1) : d160704 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13504, d160704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13504, d160704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13505 q = 1) (hb : d159762 q = 1) : d160705 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13505, d160705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13505, d160705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31644 (p : Pattern) (ha : d13509 p = 1) (hb : d159762 p = 1) : d160710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d159762 q = 1) : d160697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d160697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31641 q ha hb
    | true =>
      simp only [d13500, d160697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31615 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d159762 q = 1) : d160698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d160698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d160698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d159762 q = 1) : d160699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d160699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d160699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d159762 q = 1) : d160700 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31615 q ha hb
    | true =>
      simp only [d6502, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31639 q ha hb
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d159762 q = 1) : d160701 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d159762 q = 1) : d160702 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13503 q = 1) (hb : d159762 q = 1) : d160703 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d160703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13503, d160703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6505 q = 1) (hb : d159762 q = 1) : d160708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6505, d160708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6505, d160708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13508 q = 1) (hb : d159762 q = 1) : d160709 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13508, d160709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13508, d160709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13509 q = 1) (hb : d159762 q = 1) : d160710 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13509, d160710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13509, d160710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31645 (p : Pattern) (ha : d13515 p = 1) (hb : d159762 p = 1) : d160716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13506 q = 1) (hb : d159762 q = 1) : d160706 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13506, d160706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31643 q ha hb
    | true =>
      simp only [d13506, d160706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13507 q = 1) (hb : d159762 q = 1) : d160707 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13507, d160707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13507, d160707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13510 q = 1) (hb : d159762 q = 1) : d160711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d160711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31644 q ha hb
    | true =>
      simp only [d13510, d160711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13511 q = 1) (hb : d159762 q = 1) : d160712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d160712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d160712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13512 q = 1) (hb : d159762 q = 1) : d160713 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13512, d160713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13512, d160713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13513 q = 1) (hb : d159762 q = 1) : d160714 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13513, d160714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13513, d160714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13514 q = 1) (hb : d159762 q = 1) : d160715 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13514, d160715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13514, d160715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13515 q = 1) (hb : d159762 q = 1) : d160716 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13515, d160716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13515, d160716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31646 (p : Pattern) (ha : d13528 p = 1) (hb : d159762 p = 1) : d160724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13510 q = 1) (hb : d159762 q = 1) : d160711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d160711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31644 q ha hb
    | true =>
      simp only [d13510, d160711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13511 q = 1) (hb : d159762 q = 1) : d160712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d160712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d160712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d159762 q = 1) : d160719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d160719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31617 q ha hb
    | true =>
      simp only [d13523, d160719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d159762 q = 1) : d160720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d160720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d160720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13525 q = 1) (hb : d159762 q = 1) : d160721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13525, d160721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13525, d160721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13526 q = 1) (hb : d159762 q = 1) : d160722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13526, d160722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13526, d160722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13527 q = 1) (hb : d159762 q = 1) : d160723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13527, d160723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13527, d160723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13528 q = 1) (hb : d159762 q = 1) : d160724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13528, d160724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13528, d160724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31647 (p : Pattern) (ha : d13569 p = 1) (hb : d159762 p = 1) : d160710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13500 q = 1) (hb : d159762 q = 1) : d160697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d160697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31641 q ha hb
    | true =>
      simp only [d13500, d160697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31615 q ha hb
  have h2 (q : Pattern) (ha : d13501 q = 1) (hb : d159762 q = 1) : d160698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d160698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13501, d160698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d159762 q = 1) : d160699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d160699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13502, d160699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6502 q = 1) (hb : d159762 q = 1) : d160700 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6502, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31615 q ha hb
    | true =>
      simp only [d6502, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31639 q ha hb
  have h5 (q : Pattern) (ha : d6503 q = 1) (hb : d159762 q = 1) : d160701 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6503, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6503, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6504 q = 1) (hb : d159762 q = 1) : d160702 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6504, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6504, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13503 q = 1) (hb : d159762 q = 1) : d160703 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d160703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13503, d160703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13517 q = 1) (hb : d159762 q = 1) : d160700 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31615 q ha hb
    | true =>
      simp only [d13517, d160700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31616 q ha hb
  have h9 (q : Pattern) (ha : d13518 q = 1) (hb : d159762 q = 1) : d160701 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13518, d160701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13519 q = 1) (hb : d159762 q = 1) : d160702 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13519, d160702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13520 q = 1) (hb : d159762 q = 1) : d160708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13520, d160708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13520, d160708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13568 q = 1) (hb : d159762 q = 1) : d160709 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13568, d160709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13568, d160709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13569 q = 1) (hb : d159762 q = 1) : d160710 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13569, d160710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13569, d160710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro31648 (p : Pattern) (ha : d13575 p = 1) (hb : d159762 p = 1) : d160730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d159762 q = 1) : d160711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d160711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31647 q ha hb
    | true =>
      simp only [d13570, d160711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d159762 q = 1) : d160712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d160712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d160712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13572 q = 1) (hb : d159762 q = 1) : d160727 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13572, d160727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13572, d160727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13573 q = 1) (hb : d159762 q = 1) : d160728 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13573, d160728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13573, d160728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13574 q = 1) (hb : d159762 q = 1) : d160729 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13574, d160729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13574, d160729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13575 q = 1) (hb : d159762 q = 1) : d160730 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13575, d160730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13575, d160730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31649 (p : Pattern) (ha : d115464 p = 1) (hb : d159762 p = 1) : d160736 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13529 q = 1) (hb : d159762 q = 1) : d160725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13529, d160725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31645 q ha hb
    | true =>
      simp only [d13529, d160725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31646 q ha hb
  have h2 (q : Pattern) (ha : d115460 q = 1) (hb : d159762 q = 1) : d160726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d160726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115460, d160726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13576 q = 1) (hb : d159762 q = 1) : d160731 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13576, d160731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31648 q ha hb
    | true =>
      simp only [d13576, d160731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13577 q = 1) (hb : d159762 q = 1) : d160732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13577, d160732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13577, d160732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115461 q = 1) (hb : d159762 q = 1) : d160733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d160733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115461, d160733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115462 q = 1) (hb : d159762 q = 1) : d160734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d160734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115462, d160734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115463 q = 1) (hb : d159762 q = 1) : d160735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d160735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115463, d160735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115464 q = 1) (hb : d159762 q = 1) : d160736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d160736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115464, d160736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31650 (p : Pattern) (ha : d115470 p = 1) (hb : d159762 p = 1) : d160753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13314 q = 1) (hb : d159762 q = 1) : d160573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13314, d160573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13314, d160573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31606 q ha hb
  have h2 (q : Pattern) (ha : d13315 q = 1) (hb : d159762 q = 1) : d160574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13315, d160574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13315, d160574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13324 q = 1) (hb : d159762 q = 1) : d160583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d160583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31606 q ha hb
    | true =>
      simp only [d13324, d160583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31609 q ha hb
  have h4 (q : Pattern) (ha : d13325 q = 1) (hb : d159762 q = 1) : d160584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d160584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13325, d160584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13326 q = 1) (hb : d159762 q = 1) : d160585 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13326, d160585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13326, d160585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115448 q = 1) (hb : d159762 q = 1) : d160655 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d160655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31629 q ha hb
    | true =>
      simp only [d115448, d160655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31637 q ha hb
  have h7 (q : Pattern) (ha : d13467 q = 1) (hb : d159762 q = 1) : d160668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13467, d160668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31612 q ha hb
    | true =>
      simp only [d13467, d160668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31613 q ha hb
  have h8 (q : Pattern) (ha : d115449 q = 1) (hb : d159762 q = 1) : d160669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d160669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115449, d160669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115450 q = 1) (hb : d159762 q = 1) : d160670 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d160670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115450, d160670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115451 q = 1) (hb : d159762 q = 1) : d160671 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d160671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115451, d160671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115455 q = 1) (hb : d159762 q = 1) : d160675 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d160675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115455, d160675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31638 q ha hb
  have h12 (q : Pattern) (ha : d13476 q = 1) (hb : d159762 q = 1) : d160677 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13476, d160677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13476, d160677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31614 q ha hb
  have h13 (q : Pattern) (ha : d115456 q = 1) (hb : d159762 q = 1) : d160678 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d160678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115456, d160678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115457 q = 1) (hb : d159762 q = 1) : d160679 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d160679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115457, d160679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115458 q = 1) (hb : d159762 q = 1) : d160680 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d160680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115458, d160680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115459 q = 1) (hb : d159762 q = 1) : d160681 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d160681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115459, d160681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115465 q = 1) (hb : d159762 q = 1) : d160737 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d160737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115465, d160737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31649 q ha hb
  have h18 (q : Pattern) (ha : d13593 q = 1) (hb : d159762 q = 1) : d160748 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13593, d160748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13593, d160748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31619 q ha hb
  have h19 (q : Pattern) (ha : d115466 q = 1) (hb : d159762 q = 1) : d160749 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d160749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115466, d160749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115467 q = 1) (hb : d159762 q = 1) : d160750 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d160750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115467, d160750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115468 q = 1) (hb : d159762 q = 1) : d160751 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d160751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115468, d160751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115469 q = 1) (hb : d159762 q = 1) : d160752 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d160752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115469, d160752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115470 q = 1) (hb : d159762 q = 1) : d160753 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d160753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115470, d160753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro31651 (p : Pattern) (ha : d115476 p = 1) (hb : d159762 p = 1) : d160759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115471 q = 1) (hb : d159762 q = 1) : d160754 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d160754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115471, d160754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31650 q ha hb
  have h2 (q : Pattern) (ha : d115472 q = 1) (hb : d159762 q = 1) : d160755 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d160755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115472, d160755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115473 q = 1) (hb : d159762 q = 1) : d160756 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d160756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115473, d160756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115474 q = 1) (hb : d159762 q = 1) : d160757 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d160757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115474, d160757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115475 q = 1) (hb : d159762 q = 1) : d160758 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d160758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115475, d160758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115476 q = 1) (hb : d159762 q = 1) : d160759 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d160759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115476, d160759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31652 (p : Pattern) (ha : d5237 p = 1) (hb : d159762 p = 1) : d160767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2068 q = 1) (hb : d100904 q = 1) : d2068 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2069 q = 1) (hb : d159761 q = 1) : d160766 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d159761, d160766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2069, d159761, d160766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5237 q = 1) (hb : d159762 q = 1) : d160767 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5237, d159762, d160767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5237, d159762, d160767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31653 (p : Pattern) (ha : d5252 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d5250 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5251 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d5251, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5252 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5252, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5252, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31654 (p : Pattern) (ha : d13609 p = 1) (hb : d159762 p = 1) : d160765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2038 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2056 q = 1) (hb : d100904 q = 1) : d2056 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2057 q = 1) (hb : d159761 q = 1) : d160764 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d159761, d160764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2057, d159761, d160764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13609 q = 1) (hb : d159762 q = 1) : d160765 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13609, d159762, d160765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13609, d159762, d160765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31655 (p : Pattern) (ha : d13614 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2068 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2071 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2071, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13614 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13614, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31656 (p : Pattern) (ha : d13620 p = 1) (hb : d159762 p = 1) : d160777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13610 q = 1) (hb : d159762 q = 1) : d160768 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d160768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31654 q ha hb
    | true =>
      simp only [d13610, d160768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31652 q ha hb
  have h2 (q : Pattern) (ha : d13611 q = 1) (hb : d159762 q = 1) : d160769 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d160769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d160769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d159762 q = 1) : d160770 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d160770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d160770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d159762 q = 1) : d160771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31652 q ha hb
    | true =>
      simp only [d5253, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31653 q ha hb
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d159762 q = 1) : d160772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d159762 q = 1) : d160773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13613 q = 1) (hb : d159762 q = 1) : d160774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d160774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13613, d160774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13615 q = 1) (hb : d159762 q = 1) : d160771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31652 q ha hb
    | true =>
      simp only [d13615, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31655 q ha hb
  have h9 (q : Pattern) (ha : d13616 q = 1) (hb : d159762 q = 1) : d160772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13617 q = 1) (hb : d159762 q = 1) : d160773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13618 q = 1) (hb : d159762 q = 1) : d160775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d160775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13618, d160775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13619 q = 1) (hb : d159762 q = 1) : d160776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13619, d160776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13619, d160776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13620 q = 1) (hb : d159762 q = 1) : d160777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13620, d160777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13620, d160777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro31657 (p : Pattern) (ha : d13624 p = 1) (hb : d159762 p = 1) : d160781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13615 q = 1) (hb : d159762 q = 1) : d160771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31652 q ha hb
    | true =>
      simp only [d13615, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31655 q ha hb
  have h2 (q : Pattern) (ha : d13616 q = 1) (hb : d159762 q = 1) : d160772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13616, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13617 q = 1) (hb : d159762 q = 1) : d160773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13617, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13618 q = 1) (hb : d159762 q = 1) : d160775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13618, d160775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13618, d160775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13623 q = 1) (hb : d159762 q = 1) : d160780 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13623, d160780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13623, d160780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13624 q = 1) (hb : d159762 q = 1) : d160781 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13624, d160781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13624, d160781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31658 (p : Pattern) (ha : d13630 p = 1) (hb : d159762 p = 1) : d160787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31656 q ha hb
    | true =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d159762 q = 1) : d160784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d159762 q = 1) : d160785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d159762 q = 1) : d160786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d160786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d160786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13630 q = 1) (hb : d159762 q = 1) : d160787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13630, d160787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13630, d160787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31659 (p : Pattern) (ha : d13634 p = 1) (hb : d159762 p = 1) : d160791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d159762 q = 1) : d160788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d159762 q = 1) : d160789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d160789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d160789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d159762 q = 1) : d160790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d160790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d160790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13634 q = 1) (hb : d159762 q = 1) : d160791 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13634, d160791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13634, d160791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31660 (p : Pattern) (ha : d13640 p = 1) (hb : d159762 p = 1) : d160797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d159762 q = 1) : d160792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d160792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31658 q ha hb
    | true =>
      simp only [d13635, d160792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31659 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d159762 q = 1) : d160793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d160793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d160793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d159762 q = 1) : d160794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d160794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d160794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d159762 q = 1) : d160795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d160795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d160795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d159762 q = 1) : d160796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d160796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d160796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13640 q = 1) (hb : d159762 q = 1) : d160797 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13640, d160797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13640, d160797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31661 (p : Pattern) (ha : d13643 p = 1) (hb : d159762 p = 1) : d160800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31656 q ha hb
    | true =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d159762 q = 1) : d160784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d159762 q = 1) : d160785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13629 q = 1) (hb : d159762 q = 1) : d160786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d160786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13629, d160786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13643 q = 1) (hb : d159762 q = 1) : d160800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13643, d160800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13643, d160800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31662 (p : Pattern) (ha : d13644 p = 1) (hb : d159762 p = 1) : d160801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d159762 q = 1) : d160788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d159762 q = 1) : d160789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d160789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d160789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13633 q = 1) (hb : d159762 q = 1) : d160790 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13633, d160790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13633, d160790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13644 q = 1) (hb : d159762 q = 1) : d160801 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13644, d160801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13644, d160801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31663 (p : Pattern) (ha : d13650 p = 1) (hb : d159762 p = 1) : d160807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13635 q = 1) (hb : d159762 q = 1) : d160792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d160792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31658 q ha hb
    | true =>
      simp only [d13635, d160792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31659 q ha hb
  have h2 (q : Pattern) (ha : d13636 q = 1) (hb : d159762 q = 1) : d160793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d160793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d160793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13637 q = 1) (hb : d159762 q = 1) : d160794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d160794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13637, d160794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13638 q = 1) (hb : d159762 q = 1) : d160795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d160795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d160795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13639 q = 1) (hb : d159762 q = 1) : d160796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d160796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d160796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13645 q = 1) (hb : d159762 q = 1) : d160802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d160802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31661 q ha hb
    | true =>
      simp only [d13645, d160802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31662 q ha hb
  have h7 (q : Pattern) (ha : d13646 q = 1) (hb : d159762 q = 1) : d160803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d160803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d160803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13647 q = 1) (hb : d159762 q = 1) : d160804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d160804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13647, d160804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13648 q = 1) (hb : d159762 q = 1) : d160805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d160805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d160805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13649 q = 1) (hb : d159762 q = 1) : d160806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d160806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d160806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13650 q = 1) (hb : d159762 q = 1) : d160807 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13650, d160807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13650, d160807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31664 (p : Pattern) (ha : d13693 p = 1) (hb : d159762 p = 1) : d160777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13610 q = 1) (hb : d159762 q = 1) : d160768 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d160768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31654 q ha hb
    | true =>
      simp only [d13610, d160768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31652 q ha hb
  have h2 (q : Pattern) (ha : d13611 q = 1) (hb : d159762 q = 1) : d160769 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d160769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d160769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d159762 q = 1) : d160770 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d160770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d160770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5253 q = 1) (hb : d159762 q = 1) : d160771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31652 q ha hb
    | true =>
      simp only [d5253, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31653 q ha hb
  have h5 (q : Pattern) (ha : d5254 q = 1) (hb : d159762 q = 1) : d160772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5255 q = 1) (hb : d159762 q = 1) : d160773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13613 q = 1) (hb : d159762 q = 1) : d160774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d160774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13613, d160774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5256 q = 1) (hb : d159762 q = 1) : d160775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5256, d160775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5256, d160775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13692 q = 1) (hb : d159762 q = 1) : d160776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13692, d160776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13692, d160776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13693 q = 1) (hb : d159762 q = 1) : d160777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13693, d160777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13693, d160777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31665 (p : Pattern) (ha : d13703 p = 1) (hb : d159762 p = 1) : d160787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31664 q ha hb
    | true =>
      simp only [d13694, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d159762 q = 1) : d160784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d159762 q = 1) : d160785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d159762 q = 1) : d160786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d160786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d160786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13703 q = 1) (hb : d159762 q = 1) : d160787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13703, d160787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13703, d160787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31666 (p : Pattern) (ha : d13787 p = 1) (hb : d159762 p = 1) : d160886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13777 q = 1) (hb : d159762 q = 1) : d160792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13777, d160792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31665 q ha hb
    | true =>
      simp only [d13777, d160792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31659 q ha hb
  have h2 (q : Pattern) (ha : d13778 q = 1) (hb : d159762 q = 1) : d160793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13778, d160793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13778, d160793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13779 q = 1) (hb : d159762 q = 1) : d160794 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13779, d160794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13779, d160794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13780 q = 1) (hb : d159762 q = 1) : d160795 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13780, d160795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13780, d160795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13781 q = 1) (hb : d159762 q = 1) : d160796 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13781, d160796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13781, d160796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13782 q = 1) (hb : d159762 q = 1) : d160881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d160881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31659 q ha hb
    | true =>
      simp only [d13782, d160881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13783 q = 1) (hb : d159762 q = 1) : d160882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d160882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d160882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13784 q = 1) (hb : d159762 q = 1) : d160883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d160883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13784, d160883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13785 q = 1) (hb : d159762 q = 1) : d160884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d160884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d160884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13786 q = 1) (hb : d159762 q = 1) : d160885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d160885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d160885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13787 q = 1) (hb : d159762 q = 1) : d160886 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13787, d160886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13787, d160886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31667 (p : Pattern) (ha : d13793 p = 1) (hb : d159762 p = 1) : d160892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13782 q = 1) (hb : d159762 q = 1) : d160881 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13782, d160881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31659 q ha hb
    | true =>
      simp only [d13782, d160881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13783 q = 1) (hb : d159762 q = 1) : d160882 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13783, d160882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13783, d160882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13784 q = 1) (hb : d159762 q = 1) : d160883 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13784, d160883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13784, d160883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13785 q = 1) (hb : d159762 q = 1) : d160884 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13785, d160884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13785, d160884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13786 q = 1) (hb : d159762 q = 1) : d160885 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13786, d160885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13786, d160885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13788 q = 1) (hb : d159762 q = 1) : d160887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d160887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31662 q ha hb
    | true =>
      simp only [d13788, d160887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13789 q = 1) (hb : d159762 q = 1) : d160888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d160888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d160888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13790 q = 1) (hb : d159762 q = 1) : d160889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d160889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13790, d160889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13791 q = 1) (hb : d159762 q = 1) : d160890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d160890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d160890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13792 q = 1) (hb : d159762 q = 1) : d160891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d160891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d160891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13793 q = 1) (hb : d159762 q = 1) : d160892 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13793, d160892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13793, d160892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31668 (p : Pattern) (ha : d13802 p = 1) (hb : d159762 p = 1) : d160901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13788 q = 1) (hb : d159762 q = 1) : d160887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13788, d160887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31662 q ha hb
    | true =>
      simp only [d13788, d160887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13789 q = 1) (hb : d159762 q = 1) : d160888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13789, d160888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13789, d160888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13790 q = 1) (hb : d159762 q = 1) : d160889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13790, d160889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13790, d160889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13791 q = 1) (hb : d159762 q = 1) : d160890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13791, d160890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13791, d160890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13792 q = 1) (hb : d159762 q = 1) : d160891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13792, d160891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13792, d160891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13802 q = 1) (hb : d159762 q = 1) : d160901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13802, d160901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13802, d160901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31669 (p : Pattern) (ha : d6642 p = 1) (hb : d159762 p = 1) : d160921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2343 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2349 q = 1) (hb : d100904 q = 1) : d2349 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2350 q = 1) (hb : d159761 q = 1) : d160920 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d159761, d160920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2350, d159761, d160920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6642 q = 1) (hb : d159762 q = 1) : d160921 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, d159762, d160921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6642, d159762, d160921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31670 (p : Pattern) (ha : d13843 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2349 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2355 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2355, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13843 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13843, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31671 (p : Pattern) (ha : d13849 p = 1) (hb : d159762 p = 1) : d160943 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13844 q = 1) (hb : d159762 q = 1) : d160925 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31669 q ha hb
    | true =>
      simp only [d13844, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31670 q ha hb
  have h2 (q : Pattern) (ha : d13845 q = 1) (hb : d159762 q = 1) : d160926 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13846 q = 1) (hb : d159762 q = 1) : d160927 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13847 q = 1) (hb : d159762 q = 1) : d160933 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d160933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13847, d160933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13848 q = 1) (hb : d159762 q = 1) : d160942 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13848, d160942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13848, d160942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13849 q = 1) (hb : d159762 q = 1) : d160943 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13849, d160943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13849, d160943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31672 (p : Pattern) (ha : d13913 p = 1) (hb : d159762 p = 1) : d160966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13850 q = 1) (hb : d159762 q = 1) : d160944 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d160944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31671 q ha hb
    | true =>
      simp only [d13850, d160944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13851 q = 1) (hb : d159762 q = 1) : d160945 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d160945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d160945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13910 q = 1) (hb : d159762 q = 1) : d160963 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13910, d160963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13910, d160963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13911 q = 1) (hb : d159762 q = 1) : d160964 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13911, d160964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13911, d160964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13912 q = 1) (hb : d159762 q = 1) : d160965 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13912, d160965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13912, d160965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13913 q = 1) (hb : d159762 q = 1) : d160966 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13913, d160966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13913, d160966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31673 (p : Pattern) (ha : d13919 p = 1) (hb : d159762 p = 1) : d160972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13914 q = 1) (hb : d159762 q = 1) : d160967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13914, d160967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31672 q ha hb
    | true =>
      simp only [d13914, d160967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13915 q = 1) (hb : d159762 q = 1) : d160968 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13915, d160968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13915, d160968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13916 q = 1) (hb : d159762 q = 1) : d160969 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13916, d160969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13916, d160969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13917 q = 1) (hb : d159762 q = 1) : d160970 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13917, d160970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13917, d160970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13918 q = 1) (hb : d159762 q = 1) : d160971 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13918, d160971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13918, d160971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13919 q = 1) (hb : d159762 q = 1) : d160972 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13919, d160972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13919, d160972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31674 (p : Pattern) (ha : d13655 p = 1) (hb : d159762 p = 1) : d160812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31656 q ha hb
    | true =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d159762 q = 1) : d160784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d159762 q = 1) : d160785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d159762 q = 1) : d160811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d160811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d160811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13655 q = 1) (hb : d159762 q = 1) : d160812 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13655, d160812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13655, d160812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31675 (p : Pattern) (ha : d13657 p = 1) (hb : d159762 p = 1) : d160814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d159762 q = 1) : d160788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d159762 q = 1) : d160789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d160789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d160789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d159762 q = 1) : d160813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d160813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d160813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13657 q = 1) (hb : d159762 q = 1) : d160814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13657, d160814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13657, d160814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31676 (p : Pattern) (ha : d13664 p = 1) (hb : d159762 p = 1) : d160821 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31656 q ha hb
    | true =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d159762 q = 1) : d160784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d159762 q = 1) : d160819 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d160819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d160819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d159762 q = 1) : d160820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d160820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d160820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13664 q = 1) (hb : d159762 q = 1) : d160821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13664, d160821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13664, d160821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31677 (p : Pattern) (ha : d13667 p = 1) (hb : d159762 p = 1) : d160824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d159762 q = 1) : d160788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d159762 q = 1) : d160822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d160822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d160822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d159762 q = 1) : d160823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d160823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d160823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d159762 q = 1) : d160824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13667, d160824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13667, d160824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31678 (p : Pattern) (ha : d13671 p = 1) (hb : d159762 p = 1) : d160829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2147 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2038 q = 1) (hb : d100904 q = 1) : d2038 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2148 q = 1) (hb : d159761 q = 1) : d160828 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2148, d159761, d160828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2148, d159761, d160828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13671 q = 1) (hb : d159762 q = 1) : d160829 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13671, d159762, d160829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13671, d159762, d160829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31679 (p : Pattern) (ha : d13683 p = 1) (hb : d159762 p = 1) : d160834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13681 q = 1) (hb : d100904 q = 1) : d13681 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13682 q = 1) (hb : d159761 q = 1) : d160833 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d159761, d160833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13682, d159761, d160833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13683 q = 1) (hb : d159762 q = 1) : d160834 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13683, d159762, d160834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13683, d159762, d160834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31680 (p : Pattern) (ha : d13689 p = 1) (hb : d159762 p = 1) : d160840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13672 q = 1) (hb : d159762 q = 1) : d160830 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13672, d160830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31678 q ha hb
    | true =>
      simp only [d13672, d160830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31654 q ha hb
  have h2 (q : Pattern) (ha : d13673 q = 1) (hb : d159762 q = 1) : d160831 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13673, d160831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13673, d160831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13674 q = 1) (hb : d159762 q = 1) : d160832 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13674, d160832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13674, d160832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13684 q = 1) (hb : d159762 q = 1) : d160835 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13684, d160835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31654 q ha hb
    | true =>
      simp only [d13684, d160835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31679 q ha hb
  have h5 (q : Pattern) (ha : d13685 q = 1) (hb : d159762 q = 1) : d160836 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13685, d160836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13685, d160836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13686 q = 1) (hb : d159762 q = 1) : d160837 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13686, d160837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13686, d160837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13687 q = 1) (hb : d159762 q = 1) : d160838 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13687, d160838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13687, d160838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13610 q = 1) (hb : d159762 q = 1) : d160768 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d160768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31654 q ha hb
    | true =>
      simp only [d13610, d160768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31652 q ha hb
  have h9 (q : Pattern) (ha : d13611 q = 1) (hb : d159762 q = 1) : d160769 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d160769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13611, d160769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13612 q = 1) (hb : d159762 q = 1) : d160770 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d160770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13612, d160770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d5253 q = 1) (hb : d159762 q = 1) : d160771 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5253, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31652 q ha hb
    | true =>
      simp only [d5253, d160771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31653 q ha hb
  have h12 (q : Pattern) (ha : d5254 q = 1) (hb : d159762 q = 1) : d160772 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5254, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5254, d160772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5255 q = 1) (hb : d159762 q = 1) : d160773 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5255, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5255, d160773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13613 q = 1) (hb : d159762 q = 1) : d160774 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d160774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13613, d160774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13688 q = 1) (hb : d159762 q = 1) : d160839 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13688, d160839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13688, d160839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13689 q = 1) (hb : d159762 q = 1) : d160840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13689, d160840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13689, d160840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31681 (p : Pattern) (ha : d13699 p = 1) (hb : d159762 p = 1) : d160846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d159762 q = 1) : d160841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d160841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31680 q ha hb
    | true =>
      simp only [d13690, d160841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d159762 q = 1) : d160842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d160842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d160842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31664 q ha hb
    | true =>
      simp only [d13694, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d159762 q = 1) : d160843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d160843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d160843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d159762 q = 1) : d160844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d160844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d160844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d159762 q = 1) : d160845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d160845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d160845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13699 q = 1) (hb : d159762 q = 1) : d160846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13699, d160846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13699, d160846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31682 (p : Pattern) (ha : d13744 p = 1) (hb : d159762 p = 1) : d160852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31656 q ha hb
    | true =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d159762 q = 1) : d160849 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d160849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d160849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d159762 q = 1) : d160850 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d160850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d160850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d159762 q = 1) : d160851 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d160851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d160851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13744 q = 1) (hb : d159762 q = 1) : d160852 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13744, d160852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13744, d160852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31683 (p : Pattern) (ha : d115485 p = 1) (hb : d159762 p = 1) : d160858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d159762 q = 1) : d160815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d160815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31674 q ha hb
    | true =>
      simp only [d13658, d160815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31675 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d159762 q = 1) : d160816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d160816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d160816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d159762 q = 1) : d160817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d160817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d160817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d159762 q = 1) : d160818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d160818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d160818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d159762 q = 1) : d160825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d160825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31676 q ha hb
    | true =>
      simp only [d13668, d160825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31677 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d159762 q = 1) : d160826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d160826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d160826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d159762 q = 1) : d160827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d160827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d160827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d159762 q = 1) : d160847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d160847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31681 q ha hb
    | true =>
      simp only [d13704, d160847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31665 q ha hb
  have h9 (q : Pattern) (ha : d115481 q = 1) (hb : d159762 q = 1) : d160848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d160848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115481, d160848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d159762 q = 1) : d160853 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d160853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31682 q ha hb
    | true =>
      simp only [d13745, d160853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d159762 q = 1) : d160854 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d160854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d160854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115482 q = 1) (hb : d159762 q = 1) : d160855 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d160855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d160855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115483 q = 1) (hb : d159762 q = 1) : d160856 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d160856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115483, d160856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115484 q = 1) (hb : d159762 q = 1) : d160857 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d160857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115484, d160857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115485 q = 1) (hb : d159762 q = 1) : d160858 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d160858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115485, d160858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31684 (p : Pattern) (ha : d13751 p = 1) (hb : d159762 p = 1) : d160859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31656 q ha hb
    | true =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d159762 q = 1) : d160784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13628 q = 1) (hb : d159762 q = 1) : d160785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13628, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13654 q = 1) (hb : d159762 q = 1) : d160811 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d160811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d160811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13751 q = 1) (hb : d159762 q = 1) : d160859 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13751, d160859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13751, d160859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31685 (p : Pattern) (ha : d13752 p = 1) (hb : d159762 p = 1) : d160860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d159762 q = 1) : d160788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13632 q = 1) (hb : d159762 q = 1) : d160789 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13632, d160789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13632, d160789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13656 q = 1) (hb : d159762 q = 1) : d160813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13656, d160813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13656, d160813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13752 q = 1) (hb : d159762 q = 1) : d160860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13752, d160860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13752, d160860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31686 (p : Pattern) (ha : d13757 p = 1) (hb : d159762 p = 1) : d160865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31656 q ha hb
    | true =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13627 q = 1) (hb : d159762 q = 1) : d160784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13662 q = 1) (hb : d159762 q = 1) : d160819 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d160819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d160819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13663 q = 1) (hb : d159762 q = 1) : d160820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d160820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13663, d160820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13757 q = 1) (hb : d159762 q = 1) : d160865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13757, d160865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13757, d160865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31687 (p : Pattern) (ha : d13758 p = 1) (hb : d159762 p = 1) : d160866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13631 q = 1) (hb : d159762 q = 1) : d160788 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13631, d160788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13665 q = 1) (hb : d159762 q = 1) : d160822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13665, d160822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13665, d160822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13666 q = 1) (hb : d159762 q = 1) : d160823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13666, d160823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13666, d160823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13758 q = 1) (hb : d159762 q = 1) : d160866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13758, d160866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13758, d160866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31688 (p : Pattern) (ha : d13762 p = 1) (hb : d159762 p = 1) : d160870 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d159762 q = 1) : d160841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d160841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31680 q ha hb
    | true =>
      simp only [d13690, d160841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d159762 q = 1) : d160842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d160842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d160842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31664 q ha hb
    | true =>
      simp only [d13694, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d159762 q = 1) : d160843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d160843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d160843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d159762 q = 1) : d160844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d160844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d160844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d159762 q = 1) : d160845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d160845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d160845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13762 q = 1) (hb : d159762 q = 1) : d160870 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13762, d160870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13762, d160870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31689 (p : Pattern) (ha : d13763 p = 1) (hb : d159762 p = 1) : d160800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31664 q ha hb
    | true =>
      simp only [d13694, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13625 q = 1) (hb : d159762 q = 1) : d160782 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31657 q ha hb
    | true =>
      simp only [d13625, d160782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13626 q = 1) (hb : d159762 q = 1) : d160783 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13626, d160783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13700 q = 1) (hb : d159762 q = 1) : d160784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d160784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13701 q = 1) (hb : d159762 q = 1) : d160785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13701, d160785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13702 q = 1) (hb : d159762 q = 1) : d160786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d160786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13702, d160786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13763 q = 1) (hb : d159762 q = 1) : d160800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13763, d160800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13763, d160800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31690 (p : Pattern) (ha : d13769 p = 1) (hb : d159762 p = 1) : d160873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d159762 q = 1) : d160778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31656 q ha hb
    | true =>
      simp only [d13621, d160778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d159762 q = 1) : d160779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d160779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d159762 q = 1) : d160849 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d160849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d160849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d159762 q = 1) : d160850 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d160850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d160850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d159762 q = 1) : d160851 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d160851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d160851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13769 q = 1) (hb : d159762 q = 1) : d160873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13769, d160873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13769, d160873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31691 (p : Pattern) (ha : d115490 p = 1) (hb : d159762 p = 1) : d160879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13658 q = 1) (hb : d159762 q = 1) : d160815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d160815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31674 q ha hb
    | true =>
      simp only [d13658, d160815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31675 q ha hb
  have h2 (q : Pattern) (ha : d13659 q = 1) (hb : d159762 q = 1) : d160816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d160816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d160816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13660 q = 1) (hb : d159762 q = 1) : d160817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d160817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13660, d160817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13661 q = 1) (hb : d159762 q = 1) : d160818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d160818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d160818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13668 q = 1) (hb : d159762 q = 1) : d160825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d160825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31676 q ha hb
    | true =>
      simp only [d13668, d160825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31677 q ha hb
  have h6 (q : Pattern) (ha : d13669 q = 1) (hb : d159762 q = 1) : d160826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d160826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d160826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13670 q = 1) (hb : d159762 q = 1) : d160827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d160827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13670, d160827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13704 q = 1) (hb : d159762 q = 1) : d160847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d160847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31681 q ha hb
    | true =>
      simp only [d13704, d160847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31665 q ha hb
  have h9 (q : Pattern) (ha : d115481 q = 1) (hb : d159762 q = 1) : d160848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d160848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115481, d160848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13745 q = 1) (hb : d159762 q = 1) : d160853 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d160853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31682 q ha hb
    | true =>
      simp only [d13745, d160853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13746 q = 1) (hb : d159762 q = 1) : d160854 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d160854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13746, d160854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d115482 q = 1) (hb : d159762 q = 1) : d160855 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d160855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115482, d160855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115483 q = 1) (hb : d159762 q = 1) : d160856 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d160856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115483, d160856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115484 q = 1) (hb : d159762 q = 1) : d160857 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d160857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115484, d160857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13753 q = 1) (hb : d159762 q = 1) : d160861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13753, d160861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31684 q ha hb
    | true =>
      simp only [d13753, d160861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31685 q ha hb
  have h16 (q : Pattern) (ha : d13754 q = 1) (hb : d159762 q = 1) : d160862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13754, d160862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13754, d160862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13755 q = 1) (hb : d159762 q = 1) : d160863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13755, d160863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d13755, d160863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d13756 q = 1) (hb : d159762 q = 1) : d160864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13756, d160864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13756, d160864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13759 q = 1) (hb : d159762 q = 1) : d160867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13759, d160867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31686 q ha hb
    | true =>
      simp only [d13759, d160867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31687 q ha hb
  have h20 (q : Pattern) (ha : d13760 q = 1) (hb : d159762 q = 1) : d160868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13760, d160868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13760, d160868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d13761 q = 1) (hb : d159762 q = 1) : d160869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13761, d160869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d13761, d160869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d13764 q = 1) (hb : d159762 q = 1) : d160871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d160871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31688 q ha hb
    | true =>
      simp only [d13764, d160871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31689 q ha hb
  have h23 (q : Pattern) (ha : d115486 q = 1) (hb : d159762 q = 1) : d160872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d160872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115486, d160872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d13770 q = 1) (hb : d159762 q = 1) : d160874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d160874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31690 q ha hb
    | true =>
      simp only [d13770, d160874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d13771 q = 1) (hb : d159762 q = 1) : d160875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d160875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13771, d160875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d115487 q = 1) (hb : d159762 q = 1) : d160876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d160876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d115487, d160876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d115488 q = 1) (hb : d159762 q = 1) : d160877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d160877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115488, d160877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d115489 q = 1) (hb : d159762 q = 1) : d160878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d160878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115489, d160878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d115490 q = 1) (hb : d159762 q = 1) : d160879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d160879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115490, d160879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro31692 (p : Pattern) (ha : d115497 p = 1) (hb : d159762 p = 1) : d160899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13764 q = 1) (hb : d159762 q = 1) : d160871 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d160871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31688 q ha hb
    | true =>
      simp only [d13764, d160871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31689 q ha hb
  have h2 (q : Pattern) (ha : d115486 q = 1) (hb : d159762 q = 1) : d160872 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d160872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115486, d160872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13770 q = 1) (hb : d159762 q = 1) : d160874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d160874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31690 q ha hb
    | true =>
      simp only [d13770, d160874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13771 q = 1) (hb : d159762 q = 1) : d160875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d160875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13771, d160875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115487 q = 1) (hb : d159762 q = 1) : d160876 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d160876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115487, d160876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115495 q = 1) (hb : d159762 q = 1) : d160897 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d160897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115495, d160897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115496 q = 1) (hb : d159762 q = 1) : d160898 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d160898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115496, d160898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115497 q = 1) (hb : d159762 q = 1) : d160899 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d160899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115497, d160899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31693 (p : Pattern) (ha : d6648 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6646 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d100904 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6647 q = 1) (hb : d159761 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6647, d159761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6648 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6648, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6648, d159762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31694 (p : Pattern) (ha : d13808 p = 1) (hb : d159762 p = 1) : d160908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2338 q = 1) (hb : d100904 q = 1) : d2338 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2339 q = 1) (hb : d159761 q = 1) : d160907 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2339, d159761, d160907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2339, d159761, d160907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13808 q = 1) (hb : d159762 q = 1) : d160908 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13808, d159762, d160908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13808, d159762, d160908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31695 (p : Pattern) (ha : d13809 p = 1) (hb : d159762 p = 1) : d160910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d2338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2343 q = 1) (hb : d100904 q = 1) : d2343 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2344 q = 1) (hb : d159761 q = 1) : d160909 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d159761, d160909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d2344, d159761, d160909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13809 q = 1) (hb : d159762 q = 1) : d160910 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13809, d159762, d160910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13809, d159762, d160910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31696 (p : Pattern) (ha : d13822 p = 1) (hb : d159762 p = 1) : d160915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13816 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13820 q = 1) (hb : d100904 q = 1) : d13820 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13821 q = 1) (hb : d159761 q = 1) : d160914 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d159761, d160914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13821, d159761, d160914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13822 q = 1) (hb : d159762 q = 1) : d160915 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13822, d159762, d160915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13822, d159762, d160915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro31697 (p : Pattern) (ha : d13832 p = 1) (hb : d159762 p = 1) : d160930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13810 q = 1) (hb : d159762 q = 1) : d160911 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13810, d160911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31694 q ha hb
    | true =>
      simp only [d13810, d160911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31695 q ha hb
  have h2 (q : Pattern) (ha : d13811 q = 1) (hb : d159762 q = 1) : d160912 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13811, d160912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13811, d160912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13812 q = 1) (hb : d159762 q = 1) : d160913 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13812, d160913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13812, d160913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13823 q = 1) (hb : d159762 q = 1) : d160916 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13823, d160916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31695 q ha hb
    | true =>
      simp only [d13823, d160916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31696 q ha hb
  have h5 (q : Pattern) (ha : d13824 q = 1) (hb : d159762 q = 1) : d160917 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13824, d160917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13824, d160917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13825 q = 1) (hb : d159762 q = 1) : d160918 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13825, d160918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13825, d160918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13826 q = 1) (hb : d159762 q = 1) : d160919 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13826, d160919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13826, d160919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13827 q = 1) (hb : d159762 q = 1) : d160922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d160922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31695 q ha hb
    | true =>
      simp only [d13827, d160922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31669 q ha hb
  have h9 (q : Pattern) (ha : d13828 q = 1) (hb : d159762 q = 1) : d160923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d160923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d160923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13829 q = 1) (hb : d159762 q = 1) : d160924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d160924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d160924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d6649 q = 1) (hb : d159762 q = 1) : d160925 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31669 q ha hb
    | true =>
      simp only [d6649, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31693 q ha hb
  have h12 (q : Pattern) (ha : d6650 q = 1) (hb : d159762 q = 1) : d160926 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d6651 q = 1) (hb : d159762 q = 1) : d160927 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13830 q = 1) (hb : d159762 q = 1) : d160928 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d160928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13830, d160928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d13831 q = 1) (hb : d159762 q = 1) : d160929 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13831, d160929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13831, d160929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d13832 q = 1) (hb : d159762 q = 1) : d160930 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13832, d160930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d13832, d160930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro31698 (p : Pattern) (ha : d13836 p = 1) (hb : d159762 p = 1) : d160935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13827 q = 1) (hb : d159762 q = 1) : d160922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d160922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31695 q ha hb
    | true =>
      simp only [d13827, d160922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31669 q ha hb
  have h2 (q : Pattern) (ha : d13828 q = 1) (hb : d159762 q = 1) : d160923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d160923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d160923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13829 q = 1) (hb : d159762 q = 1) : d160924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d160924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d160924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d159762 q = 1) : d160925 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31669 q ha hb
    | true =>
      simp only [d6649, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31693 q ha hb
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d159762 q = 1) : d160926 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d159762 q = 1) : d160927 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13830 q = 1) (hb : d159762 q = 1) : d160928 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d160928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13830, d160928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6652 q = 1) (hb : d159762 q = 1) : d160933 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6652, d160933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6652, d160933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13835 q = 1) (hb : d159762 q = 1) : d160934 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13835, d160934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13835, d160934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13836 q = 1) (hb : d159762 q = 1) : d160935 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13836, d160935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13836, d160935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro31699 (p : Pattern) (ha : d13842 p = 1) (hb : d159762 p = 1) : d160941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13833 q = 1) (hb : d159762 q = 1) : d160931 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13833, d160931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31697 q ha hb
    | true =>
      simp only [d13833, d160931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13834 q = 1) (hb : d159762 q = 1) : d160932 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13834, d160932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13834, d160932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13837 q = 1) (hb : d159762 q = 1) : d160936 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d160936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31698 q ha hb
    | true =>
      simp only [d13837, d160936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13838 q = 1) (hb : d159762 q = 1) : d160937 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d160937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d160937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13839 q = 1) (hb : d159762 q = 1) : d160938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13839, d160938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13839, d160938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13840 q = 1) (hb : d159762 q = 1) : d160939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13840, d160939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13840, d160939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13841 q = 1) (hb : d159762 q = 1) : d160940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13841, d160940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13841, d160940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13842 q = 1) (hb : d159762 q = 1) : d160941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13842, d160941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13842, d160941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31700 (p : Pattern) (ha : d13855 p = 1) (hb : d159762 p = 1) : d160949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13837 q = 1) (hb : d159762 q = 1) : d160936 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d160936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31698 q ha hb
    | true =>
      simp only [d13837, d160936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13838 q = 1) (hb : d159762 q = 1) : d160937 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d160937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d160937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d159762 q = 1) : d160944 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d160944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31671 q ha hb
    | true =>
      simp only [d13850, d160944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d159762 q = 1) : d160945 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d160945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d160945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13852 q = 1) (hb : d159762 q = 1) : d160946 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13852, d160946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13852, d160946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13853 q = 1) (hb : d159762 q = 1) : d160947 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13853, d160947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13853, d160947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13854 q = 1) (hb : d159762 q = 1) : d160948 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13854, d160948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13854, d160948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13855 q = 1) (hb : d159762 q = 1) : d160949 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13855, d160949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13855, d160949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31701 (p : Pattern) (ha : d13896 p = 1) (hb : d159762 p = 1) : d160935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13827 q = 1) (hb : d159762 q = 1) : d160922 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d160922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31695 q ha hb
    | true =>
      simp only [d13827, d160922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31669 q ha hb
  have h2 (q : Pattern) (ha : d13828 q = 1) (hb : d159762 q = 1) : d160923 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d160923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13828, d160923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13829 q = 1) (hb : d159762 q = 1) : d160924 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d160924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13829, d160924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6649 q = 1) (hb : d159762 q = 1) : d160925 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6649, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31669 q ha hb
    | true =>
      simp only [d6649, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31693 q ha hb
  have h5 (q : Pattern) (ha : d6650 q = 1) (hb : d159762 q = 1) : d160926 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6650, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6650, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d6651 q = 1) (hb : d159762 q = 1) : d160927 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6651, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6651, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13830 q = 1) (hb : d159762 q = 1) : d160928 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d160928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13830, d160928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13844 q = 1) (hb : d159762 q = 1) : d160925 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31669 q ha hb
    | true =>
      simp only [d13844, d160925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31670 q ha hb
  have h9 (q : Pattern) (ha : d13845 q = 1) (hb : d159762 q = 1) : d160926 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13845, d160926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13846 q = 1) (hb : d159762 q = 1) : d160927 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13846, d160927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d13847 q = 1) (hb : d159762 q = 1) : d160933 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13847, d160933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13847, d160933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13895 q = 1) (hb : d159762 q = 1) : d160934 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13895, d160934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13895, d160934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13896 q = 1) (hb : d159762 q = 1) : d160935 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13896, d160935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13896, d160935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro31702 (p : Pattern) (ha : d13902 p = 1) (hb : d159762 p = 1) : d160955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d159762 q = 1) : d160936 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d160936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31701 q ha hb
    | true =>
      simp only [d13897, d160936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d159762 q = 1) : d160937 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d160937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d160937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13899 q = 1) (hb : d159762 q = 1) : d160952 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13899, d160952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13899, d160952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13900 q = 1) (hb : d159762 q = 1) : d160953 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13900, d160953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13900, d160953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13901 q = 1) (hb : d159762 q = 1) : d160954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13901, d160954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13901, d160954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13902 q = 1) (hb : d159762 q = 1) : d160955 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13902, d160955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13902, d160955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31703 (p : Pattern) (ha : d115507 p = 1) (hb : d159762 p = 1) : d160961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13856 q = 1) (hb : d159762 q = 1) : d160950 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13856, d160950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31699 q ha hb
    | true =>
      simp only [d13856, d160950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31700 q ha hb
  have h2 (q : Pattern) (ha : d115503 q = 1) (hb : d159762 q = 1) : d160951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d160951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115503, d160951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13903 q = 1) (hb : d159762 q = 1) : d160956 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13903, d160956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31702 q ha hb
    | true =>
      simp only [d13903, d160956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13904 q = 1) (hb : d159762 q = 1) : d160957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13904, d160957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13904, d160957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d159762 q = 1) : d160958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d160958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115504, d160958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d159762 q = 1) : d160959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d160959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d160959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d159762 q = 1) : d160960 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d160960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d160960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d159762 q = 1) : d160961 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d160961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d160961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro31704 (p : Pattern) (ha : d115513 p = 1) (hb : d159762 p = 1) : d160978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13641 q = 1) (hb : d159762 q = 1) : d160798 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13641, d160798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13641, d160798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31660 q ha hb
  have h2 (q : Pattern) (ha : d13642 q = 1) (hb : d159762 q = 1) : d160799 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13642, d160799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13642, d160799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13651 q = 1) (hb : d159762 q = 1) : d160808 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d160808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31660 q ha hb
    | true =>
      simp only [d13651, d160808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31663 q ha hb
  have h4 (q : Pattern) (ha : d13652 q = 1) (hb : d159762 q = 1) : d160809 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d160809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13652, d160809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13653 q = 1) (hb : d159762 q = 1) : d160810 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13653, d160810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13653, d160810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115491 q = 1) (hb : d159762 q = 1) : d160880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d160880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31683 q ha hb
    | true =>
      simp only [d115491, d160880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31691 q ha hb
  have h7 (q : Pattern) (ha : d13794 q = 1) (hb : d159762 q = 1) : d160893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13794, d160893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31666 q ha hb
    | true =>
      simp only [d13794, d160893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31667 q ha hb
  have h8 (q : Pattern) (ha : d115492 q = 1) (hb : d159762 q = 1) : d160894 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d160894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115492, d160894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115493 q = 1) (hb : d159762 q = 1) : d160895 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d160895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115493, d160895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d115494 q = 1) (hb : d159762 q = 1) : d160896 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d160896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115494, d160896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115498 q = 1) (hb : d159762 q = 1) : d160900 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d160900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115498, d160900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31692 q ha hb
  have h12 (q : Pattern) (ha : d13803 q = 1) (hb : d159762 q = 1) : d160902 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13803, d160902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13803, d160902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31668 q ha hb
  have h13 (q : Pattern) (ha : d115499 q = 1) (hb : d159762 q = 1) : d160903 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d160903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115499, d160903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115500 q = 1) (hb : d159762 q = 1) : d160904 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d160904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115500, d160904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d115501 q = 1) (hb : d159762 q = 1) : d160905 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d160905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115501, d160905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115502 q = 1) (hb : d159762 q = 1) : d160906 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d160906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115502, d160906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115508 q = 1) (hb : d159762 q = 1) : d160962 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d160962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115508, d160962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31703 q ha hb
  have h18 (q : Pattern) (ha : d13920 q = 1) (hb : d159762 q = 1) : d160973 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13920, d160973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13920, d160973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31673 q ha hb
  have h19 (q : Pattern) (ha : d115509 q = 1) (hb : d159762 q = 1) : d160974 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d160974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115509, d160974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d115510 q = 1) (hb : d159762 q = 1) : d160975 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d160975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d115510, d160975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d115511 q = 1) (hb : d159762 q = 1) : d160976 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d160976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115511, d160976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115512 q = 1) (hb : d159762 q = 1) : d160977 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d160977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115512, d160977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115513 q = 1) (hb : d159762 q = 1) : d160978 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d160978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115513, d160978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro31705 (p : Pattern) (ha : d115519 p = 1) (hb : d159762 p = 1) : d160984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d159762 q = 1) : d160979 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d160979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d160979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31704 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d159762 q = 1) : d160980 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d160980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d160980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d159762 q = 1) : d160981 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d160981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d160981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d159762 q = 1) : d160982 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d160982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d160982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d159762 q = 1) : d160983 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d160983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d160983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d159762 q = 1) : d160984 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d160984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d160984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31706 (p : Pattern) (ha : d115525 p = 1) (hb : d159762 p = 1) : d160990 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d159762 q = 1) : d160105 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d160105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31455 q ha hb
    | true =>
      simp only [d115354, d160105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31497 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d159762 q = 1) : d160313 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d160313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d160313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31543 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d159762 q = 1) : d160314 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d160314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d160314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d159762 q = 1) : d160536 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d160536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d160536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31597 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d159762 q = 1) : d160537 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d160537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d160537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d159762 q = 1) : d160538 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d160538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d160538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d159762 q = 1) : d160760 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d160760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d160760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31651 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d159762 q = 1) : d160761 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d160761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d160761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d159762 q = 1) : d160762 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d160762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d160762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d159762 q = 1) : d160763 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d160763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d160763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d159762 q = 1) : d160985 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d160985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d160985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31705 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d159762 q = 1) : d160986 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d160986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d160986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d159762 q = 1) : d160987 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d160987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d160987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d159762 q = 1) : d160988 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d160988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d160988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d159762 q = 1) : d160989 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d160989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d160989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d159762 q = 1) : d160990 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d160990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d160990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro31707 (p : Pattern) (ha : d115531 p = 1) (hb : d159762 p = 1) : d160996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d159762 q = 1) : d160991 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d160991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31706 q ha hb
    | true =>
      simp only [d115526, d160991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d159762 q = 1) : d160992 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d160992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d160992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d159762 q = 1) : d160993 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d160993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d160993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d159762 q = 1) : d160994 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d160994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d160994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d159762 q = 1) : d160995 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d160995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d160995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d159762 q = 1) : d160996 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d160996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d160996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31708 (p : Pattern) (ha : d115537 p = 1) (hb : d159762 p = 1) : d161002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d159762 q = 1) : d160997 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d160997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31707 q ha hb
    | true =>
      simp only [d115532, d160997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d159762 q = 1) : d160998 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d160998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d160998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d159762 q = 1) : d160999 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d160999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d160999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d159762 q = 1) : d161000 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d161000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d161000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d159762 q = 1) : d161001 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d161001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d161001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d159762 q = 1) : d161002 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d161002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d161002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31709 (p : Pattern) (ha : d115543 p = 1) (hb : d159762 p = 1) : d161008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d159762 q = 1) : d161003 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d161003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31708 q ha hb
    | true =>
      simp only [d115538, d161003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d159762 q = 1) : d161004 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d161004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d161004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d159762 q = 1) : d161005 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d161005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d161005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d159762 q = 1) : d161006 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d161006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d161006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d159762 q = 1) : d161007 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d161007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d161007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d159762 q = 1) : d161008 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d161008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d161008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31710 (p : Pattern) (ha : d115549 p = 1) (hb : d159762 p = 1) : d161014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d159762 q = 1) : d161009 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d161009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31709 q ha hb
    | true =>
      simp only [d115544, d161009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d159762 q = 1) : d161010 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d161010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d161010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115546 q = 1) (hb : d159762 q = 1) : d161011 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d161011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d161011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115547 q = 1) (hb : d159762 q = 1) : d161012 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d161012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d161012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115548 q = 1) (hb : d159762 q = 1) : d161013 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d161013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d161013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115549 q = 1) (hb : d159762 q = 1) : d161014 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d161014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d161014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31711 (p : Pattern) (ha : d115555 p = 1) (hb : d159762 p = 1) : d161020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d159762 q = 1) : d161015 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d161015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31710 q ha hb
    | true =>
      simp only [d115550, d161015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d159762 q = 1) : d161016 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d161016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d161016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d159762 q = 1) : d161017 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d161017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d161017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d159762 q = 1) : d161018 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d161018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d161018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d159762 q = 1) : d161019 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d161019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d161019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d159762 q = 1) : d161020 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d161020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d161020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31712 (p : Pattern) (ha : d115561 p = 1) (hb : d159762 p = 1) : d161026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d159762 q = 1) : d161021 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d161021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31711 q ha hb
    | true =>
      simp only [d115556, d161021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d159762 q = 1) : d161022 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d161022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d161022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d159762 q = 1) : d161023 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d161023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d161023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d159762 q = 1) : d161024 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d161024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d161024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d159762 q = 1) : d161025 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d161025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d161025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d159762 q = 1) : d161026 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d161026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d161026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31713 (p : Pattern) (ha : d115567 p = 1) (hb : d159762 p = 1) : d161032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d159762 q = 1) : d161027 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d161027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31712 q ha hb
    | true =>
      simp only [d115562, d161027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d159762 q = 1) : d161028 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d161028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d161028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d159762 q = 1) : d161029 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d161029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d161029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d159762 q = 1) : d161030 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d161030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d161030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d159762 q = 1) : d161031 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d161031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d161031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d159762 q = 1) : d161032 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d161032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d161032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31714 (p : Pattern) (ha : d1 p = 1) (hb : d161032 p = 1) : d161032 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d161032 q = 1) : d161032 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro31715 (p : Pattern) (ha : d53647 p = 1) (hb : d159762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31412 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31413 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31431 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31432 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
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
theorem andIntro31716 (p : Pattern) (ha : d150329 p = 1) (hb : d159762 p = 1) : d160055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d159762 q = 1) : d159817 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31423 q ha hb
    | true =>
      simp only [d12241, d159817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31404 q ha hb
  have h2 (q : Pattern) (ha : d12292 q = 1) (hb : d159762 q = 1) : d159871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d159871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12293 q = 1) (hb : d159762 q = 1) : d159872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12293, d159872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12294 q = 1) (hb : d159762 q = 1) : d159873 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d159873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12295 q = 1) (hb : d159762 q = 1) : d159874 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d159874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150329 q = 1) (hb : d159762 q = 1) : d160055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150329, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150329, d160055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31717 (p : Pattern) (ha : d150339 p = 1) (hb : d159762 p = 1) : d160092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d159762 q = 1) : d159847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31428 q ha hb
    | true =>
      simp only [d12268, d159847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31409 q ha hb
  have h2 (q : Pattern) (ha : d150335 q = 1) (hb : d159762 q = 1) : d160088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150335, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150335, d160088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150336 q = 1) (hb : d159762 q = 1) : d160089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150336, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150336, d160089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150337 q = 1) (hb : d159762 q = 1) : d160090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150337, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150337, d160090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150338 q = 1) (hb : d159762 q = 1) : d160091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150338, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150338, d160091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150339 q = 1) (hb : d159762 q = 1) : d160092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150339, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150339, d160092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31718 (p : Pattern) (ha : d150345 p = 1) (hb : d159762 p = 1) : d161043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d159762 q = 1) : d159876 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31433 q ha hb
    | true =>
      simp only [d12297, d159876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31434 q ha hb
  have h2 (q : Pattern) (ha : d12298 q = 1) (hb : d159762 q = 1) : d159877 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d159877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150327 q = 1) (hb : d159762 q = 1) : d161033 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150327, d161033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150327, d161033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150328 q = 1) (hb : d159762 q = 1) : d161034 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150328, d161034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150328, d161034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150330 q = 1) (hb : d159762 q = 1) : d160056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150330, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150330, d160056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31716 q ha hb
  have h6 (q : Pattern) (ha : d150331 q = 1) (hb : d159762 q = 1) : d161035 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150331, d161035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150331, d161035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150332 q = 1) (hb : d159762 q = 1) : d161036 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150332, d161036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150332, d161036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150333 q = 1) (hb : d159762 q = 1) : d161037 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150333, d161037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150333, d161037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150334 q = 1) (hb : d159762 q = 1) : d161038 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150334, d161038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150334, d161038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150340 q = 1) (hb : d159762 q = 1) : d160093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150340, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150340, d160093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31717 q ha hb
  have h11 (q : Pattern) (ha : d150341 q = 1) (hb : d159762 q = 1) : d161039 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150341, d161039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150341, d161039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150342 q = 1) (hb : d159762 q = 1) : d161040 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150342, d161040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150342, d161040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150343 q = 1) (hb : d159762 q = 1) : d161041 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150343, d161041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150343, d161041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150344 q = 1) (hb : d159762 q = 1) : d161042 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150344, d161042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150344, d161042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150345 q = 1) (hb : d159762 q = 1) : d161043 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150345, d161043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150345, d161043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31719 (p : Pattern) (ha : d150351 p = 1) (hb : d159762 p = 1) : d161049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31715 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150346 q = 1) (hb : d159762 q = 1) : d161044 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150346, d161044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150346, d161044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31718 q ha hb
  have h7 (q : Pattern) (ha : d150347 q = 1) (hb : d159762 q = 1) : d161045 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150347, d161045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150347, d161045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150348 q = 1) (hb : d159762 q = 1) : d161046 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150348, d161046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150348, d161046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150349 q = 1) (hb : d159762 q = 1) : d161047 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150349, d161047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150349, d161047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150350 q = 1) (hb : d159762 q = 1) : d161048 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150350, d161048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150350, d161048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150351 q = 1) (hb : d159762 q = 1) : d161049 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150351, d161049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150351, d161049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro31720 (p : Pattern) (ha : d150354 p = 1) (hb : d159762 p = 1) : d161052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12463 q = 1) (hb : d159762 q = 1) : d159921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31461 q ha hb
    | true =>
      simp only [d12463, d159921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31462 q ha hb
  have h2 (q : Pattern) (ha : d12464 q = 1) (hb : d159762 q = 1) : d159980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d159980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d159980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12465 q = 1) (hb : d159762 q = 1) : d159981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d159981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12465, d159981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12466 q = 1) (hb : d159762 q = 1) : d159982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d159982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d159982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12467 q = 1) (hb : d159762 q = 1) : d159983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d159983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d159983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150354 q = 1) (hb : d159762 q = 1) : d161052 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d161052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150354, d161052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31721 (p : Pattern) (ha : d150365 p = 1) (hb : d159762 p = 1) : d161062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150360 q = 1) (hb : d159762 q = 1) : d159955 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d159955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31493 q ha hb
    | true =>
      simp only [d150360, d159955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31468 q ha hb
  have h2 (q : Pattern) (ha : d150361 q = 1) (hb : d159762 q = 1) : d161058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d161058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150361, d161058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150362 q = 1) (hb : d159762 q = 1) : d161059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d161059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150362, d161059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150363 q = 1) (hb : d159762 q = 1) : d161060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d161060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150363, d161060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150364 q = 1) (hb : d159762 q = 1) : d161061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d161061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150364, d161061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150365 q = 1) (hb : d159762 q = 1) : d161062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d161062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150365, d161062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31722 (p : Pattern) (ha : d150371 p = 1) (hb : d159762 p = 1) : d161068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d159762 q = 1) : d159985 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d159985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31460 q ha hb
    | true =>
      simp only [d12469, d159985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31463 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d159762 q = 1) : d159986 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d159986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d159986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150352 q = 1) (hb : d159762 q = 1) : d161050 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d161050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150352, d161050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150353 q = 1) (hb : d159762 q = 1) : d161051 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d161051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150353, d161051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150355 q = 1) (hb : d159762 q = 1) : d161053 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d161053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150355, d161053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31720 q ha hb
  have h6 (q : Pattern) (ha : d150356 q = 1) (hb : d159762 q = 1) : d161054 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d161054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d161054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150357 q = 1) (hb : d159762 q = 1) : d161055 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d161055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d161055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150358 q = 1) (hb : d159762 q = 1) : d161056 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d161056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d161056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150359 q = 1) (hb : d159762 q = 1) : d161057 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d161057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d161057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150366 q = 1) (hb : d159762 q = 1) : d161063 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d161063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150366, d161063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31721 q ha hb
  have h11 (q : Pattern) (ha : d150367 q = 1) (hb : d159762 q = 1) : d161064 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d161064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d161064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150368 q = 1) (hb : d159762 q = 1) : d161065 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d161065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d161065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150369 q = 1) (hb : d159762 q = 1) : d161066 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d161066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d161066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150370 q = 1) (hb : d159762 q = 1) : d161067 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d161067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d161067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150371 q = 1) (hb : d159762 q = 1) : d161068 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d161068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d161068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31723 (p : Pattern) (ha : d150377 p = 1) (hb : d159762 p = 1) : d161074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150372 q = 1) (hb : d159762 q = 1) : d161069 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d161069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150372, d161069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31722 q ha hb
  have h2 (q : Pattern) (ha : d150373 q = 1) (hb : d159762 q = 1) : d161070 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d161070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150373, d161070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150374 q = 1) (hb : d159762 q = 1) : d161071 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d161071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150374, d161071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150375 q = 1) (hb : d159762 q = 1) : d161072 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d161072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150375, d161072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150376 q = 1) (hb : d159762 q = 1) : d161073 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d161073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150376, d161073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150377 q = 1) (hb : d159762 q = 1) : d161074 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d161074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150377, d161074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31724 (p : Pattern) (ha : d150381 p = 1) (hb : d159762 p = 1) : d161078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12718 q = 1) (hb : d159762 q = 1) : d160142 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d160142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31505 q ha hb
    | true =>
      simp only [d12718, d160142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31506 q ha hb
  have h2 (q : Pattern) (ha : d12719 q = 1) (hb : d159762 q = 1) : d160143 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d160143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d160143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12720 q = 1) (hb : d159762 q = 1) : d160144 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d160144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12720, d160144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12721 q = 1) (hb : d159762 q = 1) : d160145 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d160145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d160145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12722 q = 1) (hb : d159762 q = 1) : d160146 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d160146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d160146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150381 q = 1) (hb : d159762 q = 1) : d161078 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d161078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150381, d161078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31725 (p : Pattern) (ha : d150392 p = 1) (hb : d159762 p = 1) : d161089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150387 q = 1) (hb : d159762 q = 1) : d161084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d161084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31539 q ha hb
    | true =>
      simp only [d150387, d161084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31514 q ha hb
  have h2 (q : Pattern) (ha : d150388 q = 1) (hb : d159762 q = 1) : d161085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d161085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150388, d161085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150389 q = 1) (hb : d159762 q = 1) : d161086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d161086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150389, d161086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150390 q = 1) (hb : d159762 q = 1) : d161087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d161087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150390, d161087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150391 q = 1) (hb : d159762 q = 1) : d161088 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d161088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150391, d161088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150392 q = 1) (hb : d159762 q = 1) : d161089 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d161089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150392, d161089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31726 (p : Pattern) (ha : d150398 p = 1) (hb : d159762 p = 1) : d161095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d159762 q = 1) : d160148 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d160148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31504 q ha hb
    | true =>
      simp only [d12724, d160148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31507 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d159762 q = 1) : d160149 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d160149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d160149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150379 q = 1) (hb : d159762 q = 1) : d161076 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d161076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150379, d161076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150380 q = 1) (hb : d159762 q = 1) : d161077 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d161077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150380, d161077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150382 q = 1) (hb : d159762 q = 1) : d161079 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d161079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150382, d161079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31724 q ha hb
  have h6 (q : Pattern) (ha : d150383 q = 1) (hb : d159762 q = 1) : d161080 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d161080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d161080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150384 q = 1) (hb : d159762 q = 1) : d161081 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d161081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d161081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150385 q = 1) (hb : d159762 q = 1) : d161082 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d161082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d161082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150386 q = 1) (hb : d159762 q = 1) : d161083 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d161083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d161083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150393 q = 1) (hb : d159762 q = 1) : d161090 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d161090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150393, d161090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31725 q ha hb
  have h11 (q : Pattern) (ha : d150394 q = 1) (hb : d159762 q = 1) : d161091 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d161091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d161091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150395 q = 1) (hb : d159762 q = 1) : d161092 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d161092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d161092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150396 q = 1) (hb : d159762 q = 1) : d161093 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d161093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d161093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150397 q = 1) (hb : d159762 q = 1) : d161094 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d161094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d161094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150398 q = 1) (hb : d159762 q = 1) : d161095 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d161095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d161095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31727 (p : Pattern) (ha : d150404 p = 1) (hb : d159762 p = 1) : d161101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150399 q = 1) (hb : d159762 q = 1) : d161096 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d161096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150399, d161096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31726 q ha hb
  have h2 (q : Pattern) (ha : d150400 q = 1) (hb : d159762 q = 1) : d161097 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d161097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150400, d161097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150401 q = 1) (hb : d159762 q = 1) : d161098 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d161098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150401, d161098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150402 q = 1) (hb : d159762 q = 1) : d161099 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d161099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150402, d161099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150403 q = 1) (hb : d159762 q = 1) : d161100 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d161100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150403, d161100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150404 q = 1) (hb : d159762 q = 1) : d161101 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d161101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150404, d161101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31728 (p : Pattern) (ha : d150409 p = 1) (hb : d159762 p = 1) : d161106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12992 q = 1) (hb : d159762 q = 1) : d160353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d160353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31553 q ha hb
    | true =>
      simp only [d12992, d160353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31554 q ha hb
  have h2 (q : Pattern) (ha : d12993 q = 1) (hb : d159762 q = 1) : d160354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d160354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d160354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12994 q = 1) (hb : d159762 q = 1) : d160355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d160355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12994, d160355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12995 q = 1) (hb : d159762 q = 1) : d160356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d160356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d160356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12996 q = 1) (hb : d159762 q = 1) : d160357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d160357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d160357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150409 q = 1) (hb : d159762 q = 1) : d161106 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d161106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150409, d161106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31729 (p : Pattern) (ha : d150418 p = 1) (hb : d159762 p = 1) : d160500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d159762 q = 1) : d160487 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d160487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31593 q ha hb
    | true =>
      simp only [d13244, d160487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d159762 q = 1) : d160488 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d160488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d160488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d159762 q = 1) : d160495 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31563 q ha hb
    | true =>
      simp only [d13197, d160495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d159762 q = 1) : d160496 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d160496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150415 q = 1) (hb : d159762 q = 1) : d160497 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d160497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150415, d160497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150416 q = 1) (hb : d159762 q = 1) : d160498 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d160498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150416, d160498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150417 q = 1) (hb : d159762 q = 1) : d160499 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d160499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150417, d160499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150418 q = 1) (hb : d159762 q = 1) : d160500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d160500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150418, d160500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31730 (p : Pattern) (ha : d150424 p = 1) (hb : d159762 p = 1) : d161117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150419 q = 1) (hb : d159762 q = 1) : d161112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d161112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31729 q ha hb
    | true =>
      simp only [d150419, d161112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31564 q ha hb
  have h2 (q : Pattern) (ha : d150420 q = 1) (hb : d159762 q = 1) : d161113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d161113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150420, d161113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150421 q = 1) (hb : d159762 q = 1) : d161114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d161114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150421, d161114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150422 q = 1) (hb : d159762 q = 1) : d161115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d161115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150422, d161115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150423 q = 1) (hb : d159762 q = 1) : d161116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d161116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150423, d161116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150424 q = 1) (hb : d159762 q = 1) : d161117 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d161117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150424, d161117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31731 (p : Pattern) (ha : d150430 p = 1) (hb : d159762 p = 1) : d161123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d159762 q = 1) : d160359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d160359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31552 q ha hb
    | true =>
      simp only [d12998, d160359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31555 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d159762 q = 1) : d160360 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d160360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d160360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150407 q = 1) (hb : d159762 q = 1) : d161104 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d161104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150407, d161104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150408 q = 1) (hb : d159762 q = 1) : d161105 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d161105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150408, d161105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150410 q = 1) (hb : d159762 q = 1) : d161107 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d161107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150410, d161107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31728 q ha hb
  have h6 (q : Pattern) (ha : d150411 q = 1) (hb : d159762 q = 1) : d161108 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d161108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d161108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150412 q = 1) (hb : d159762 q = 1) : d161109 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d161109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d161109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150413 q = 1) (hb : d159762 q = 1) : d161110 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d161110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d161110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150414 q = 1) (hb : d159762 q = 1) : d161111 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d161111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d161111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150425 q = 1) (hb : d159762 q = 1) : d161118 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d161118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150425, d161118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31730 q ha hb
  have h11 (q : Pattern) (ha : d150426 q = 1) (hb : d159762 q = 1) : d161119 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d161119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d161119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150427 q = 1) (hb : d159762 q = 1) : d161120 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d161120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d161120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150428 q = 1) (hb : d159762 q = 1) : d161121 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d161121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d161121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150429 q = 1) (hb : d159762 q = 1) : d161122 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d161122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d161122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150430 q = 1) (hb : d159762 q = 1) : d161123 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d161123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d161123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31732 (p : Pattern) (ha : d150436 p = 1) (hb : d159762 p = 1) : d161129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150431 q = 1) (hb : d159762 q = 1) : d161124 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d161124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150431, d161124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31731 q ha hb
  have h2 (q : Pattern) (ha : d150432 q = 1) (hb : d159762 q = 1) : d161125 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d161125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150432, d161125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150433 q = 1) (hb : d159762 q = 1) : d161126 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d161126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150433, d161126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150434 q = 1) (hb : d159762 q = 1) : d161127 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d161127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150434, d161127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150435 q = 1) (hb : d159762 q = 1) : d161128 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d161128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150435, d161128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150436 q = 1) (hb : d159762 q = 1) : d161129 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d161129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150436, d161129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31733 (p : Pattern) (ha : d150442 p = 1) (hb : d159762 p = 1) : d161135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13318 q = 1) (hb : d159762 q = 1) : d160577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d160577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31607 q ha hb
    | true =>
      simp only [d13318, d160577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31608 q ha hb
  have h2 (q : Pattern) (ha : d13319 q = 1) (hb : d159762 q = 1) : d160578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d160578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d160578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13320 q = 1) (hb : d159762 q = 1) : d160579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d160579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13320, d160579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13321 q = 1) (hb : d159762 q = 1) : d160580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d160580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d160580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13322 q = 1) (hb : d159762 q = 1) : d160581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d160581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d160581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150442 q = 1) (hb : d159762 q = 1) : d161135 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d161135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150442, d161135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31734 (p : Pattern) (ha : d150451 p = 1) (hb : d159762 p = 1) : d160724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d159762 q = 1) : d160711 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d160711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31647 q ha hb
    | true =>
      simp only [d13570, d160711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d159762 q = 1) : d160712 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d160712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d160712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d159762 q = 1) : d160719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d160719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31617 q ha hb
    | true =>
      simp only [d13523, d160719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d159762 q = 1) : d160720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d160720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d160720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150448 q = 1) (hb : d159762 q = 1) : d160721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d160721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150448, d160721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150449 q = 1) (hb : d159762 q = 1) : d160722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d160722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150449, d160722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150450 q = 1) (hb : d159762 q = 1) : d160723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d160723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150450, d160723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150451 q = 1) (hb : d159762 q = 1) : d160724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d160724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150451, d160724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31735 (p : Pattern) (ha : d150457 p = 1) (hb : d159762 p = 1) : d161146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150452 q = 1) (hb : d159762 q = 1) : d161141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d161141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31734 q ha hb
    | true =>
      simp only [d150452, d161141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31618 q ha hb
  have h2 (q : Pattern) (ha : d150453 q = 1) (hb : d159762 q = 1) : d161142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d161142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150453, d161142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150454 q = 1) (hb : d159762 q = 1) : d161143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d161143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150454, d161143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150455 q = 1) (hb : d159762 q = 1) : d161144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d161144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150455, d161144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150456 q = 1) (hb : d159762 q = 1) : d161145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d161145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150456, d161145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150457 q = 1) (hb : d159762 q = 1) : d161146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d161146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150457, d161146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31736 (p : Pattern) (ha : d150463 p = 1) (hb : d159762 p = 1) : d161152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d159762 q = 1) : d160583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d160583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31606 q ha hb
    | true =>
      simp only [d13324, d160583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31609 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d159762 q = 1) : d160584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d160584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d160584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150440 q = 1) (hb : d159762 q = 1) : d161133 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d161133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150440, d161133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150441 q = 1) (hb : d159762 q = 1) : d161134 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d161134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150441, d161134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150443 q = 1) (hb : d159762 q = 1) : d161136 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d161136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150443, d161136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31733 q ha hb
  have h6 (q : Pattern) (ha : d150444 q = 1) (hb : d159762 q = 1) : d161137 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d161137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d161137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150445 q = 1) (hb : d159762 q = 1) : d161138 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d161138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d161138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150446 q = 1) (hb : d159762 q = 1) : d161139 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d161139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d161139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150447 q = 1) (hb : d159762 q = 1) : d161140 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d161140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d161140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150458 q = 1) (hb : d159762 q = 1) : d161147 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d161147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150458, d161147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31735 q ha hb
  have h11 (q : Pattern) (ha : d150459 q = 1) (hb : d159762 q = 1) : d161148 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d161148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d161148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150460 q = 1) (hb : d159762 q = 1) : d161149 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d161149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d161149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150461 q = 1) (hb : d159762 q = 1) : d161150 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d161150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d161150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150462 q = 1) (hb : d159762 q = 1) : d161151 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d161151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d161151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150463 q = 1) (hb : d159762 q = 1) : d161152 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d161152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d161152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31737 (p : Pattern) (ha : d150469 p = 1) (hb : d159762 p = 1) : d161158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150464 q = 1) (hb : d159762 q = 1) : d161153 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d161153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150464, d161153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31736 q ha hb
  have h2 (q : Pattern) (ha : d150465 q = 1) (hb : d159762 q = 1) : d161154 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d161154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150465, d161154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150466 q = 1) (hb : d159762 q = 1) : d161155 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d161155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150466, d161155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150467 q = 1) (hb : d159762 q = 1) : d161156 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d161156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150467, d161156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150468 q = 1) (hb : d159762 q = 1) : d161157 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d161157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150468, d161157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150469 q = 1) (hb : d159762 q = 1) : d161158 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d161158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150469, d161158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31738 (p : Pattern) (ha : d150476 p = 1) (hb : d159762 p = 1) : d161165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13645 q = 1) (hb : d159762 q = 1) : d160802 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d160802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31661 q ha hb
    | true =>
      simp only [d13645, d160802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31662 q ha hb
  have h2 (q : Pattern) (ha : d13646 q = 1) (hb : d159762 q = 1) : d160803 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d160803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d160803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13647 q = 1) (hb : d159762 q = 1) : d160804 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d160804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13647, d160804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13648 q = 1) (hb : d159762 q = 1) : d160805 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d160805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d160805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13649 q = 1) (hb : d159762 q = 1) : d160806 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d160806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d160806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150476 q = 1) (hb : d159762 q = 1) : d161165 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d161165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150476, d161165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31739 (p : Pattern) (ha : d150485 p = 1) (hb : d159762 p = 1) : d160949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d159762 q = 1) : d160936 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d160936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31701 q ha hb
    | true =>
      simp only [d13897, d160936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d159762 q = 1) : d160937 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d160937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d160937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d159762 q = 1) : d160944 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d160944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31671 q ha hb
    | true =>
      simp only [d13850, d160944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d159762 q = 1) : d160945 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d160945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d160945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150482 q = 1) (hb : d159762 q = 1) : d160946 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d160946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150482, d160946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150483 q = 1) (hb : d159762 q = 1) : d160947 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d160947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150483, d160947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150484 q = 1) (hb : d159762 q = 1) : d160948 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d160948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150484, d160948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150485 q = 1) (hb : d159762 q = 1) : d160949 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d160949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150485, d160949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro31740 (p : Pattern) (ha : d150491 p = 1) (hb : d159762 p = 1) : d161176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150486 q = 1) (hb : d159762 q = 1) : d161171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d161171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31739 q ha hb
    | true =>
      simp only [d150486, d161171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31672 q ha hb
  have h2 (q : Pattern) (ha : d150487 q = 1) (hb : d159762 q = 1) : d161172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d161172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150487, d161172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150488 q = 1) (hb : d159762 q = 1) : d161173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d161173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150488, d161173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150489 q = 1) (hb : d159762 q = 1) : d161174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d161174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150489, d161174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150490 q = 1) (hb : d159762 q = 1) : d161175 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d161175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150490, d161175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150491 q = 1) (hb : d159762 q = 1) : d161176 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d161176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150491, d161176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31741 (p : Pattern) (ha : d150497 p = 1) (hb : d159762 p = 1) : d161182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d159762 q = 1) : d160808 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d160808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31660 q ha hb
    | true =>
      simp only [d13651, d160808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31663 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d159762 q = 1) : d160809 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d160809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d160809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150474 q = 1) (hb : d159762 q = 1) : d161163 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d161163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150474, d161163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150475 q = 1) (hb : d159762 q = 1) : d161164 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d161164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150475, d161164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150477 q = 1) (hb : d159762 q = 1) : d161166 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d161166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150477, d161166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31738 q ha hb
  have h6 (q : Pattern) (ha : d150478 q = 1) (hb : d159762 q = 1) : d161167 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d161167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d161167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150479 q = 1) (hb : d159762 q = 1) : d161168 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d161168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d161168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150480 q = 1) (hb : d159762 q = 1) : d161169 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d161169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d161169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150481 q = 1) (hb : d159762 q = 1) : d161170 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d161170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d161170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150492 q = 1) (hb : d159762 q = 1) : d161177 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d161177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150492, d161177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31740 q ha hb
  have h11 (q : Pattern) (ha : d150493 q = 1) (hb : d159762 q = 1) : d161178 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d161178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d161178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150494 q = 1) (hb : d159762 q = 1) : d161179 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d161179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d161179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150495 q = 1) (hb : d159762 q = 1) : d161180 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d161180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d161180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150496 q = 1) (hb : d159762 q = 1) : d161181 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d161181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d161181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150497 q = 1) (hb : d159762 q = 1) : d161182 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d161182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d161182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro31742 (p : Pattern) (ha : d150503 p = 1) (hb : d159762 p = 1) : d161188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150498 q = 1) (hb : d159762 q = 1) : d161183 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d161183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150498, d161183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31741 q ha hb
  have h2 (q : Pattern) (ha : d150499 q = 1) (hb : d159762 q = 1) : d161184 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d161184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150499, d161184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150500 q = 1) (hb : d159762 q = 1) : d161185 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d161185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150500, d161185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150501 q = 1) (hb : d159762 q = 1) : d161186 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d161186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150501, d161186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150502 q = 1) (hb : d159762 q = 1) : d161187 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d161187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150502, d161187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150503 q = 1) (hb : d159762 q = 1) : d161188 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d161188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150503, d161188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro31743 (p : Pattern) (ha : d150509 p = 1) (hb : d159762 p = 1) : d161194 p = 1 := by
  have h0 (q : Pattern) (ha : d150378 q = 1) (hb : d159762 q = 1) : d161075 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d161075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31719 q ha hb
    | true =>
      simp only [d150378, d161075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31723 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150405 q = 1) (hb : d159762 q = 1) : d161102 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d161102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150405, d161102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31727 q ha hb
  have h3 (q : Pattern) (ha : d150406 q = 1) (hb : d159762 q = 1) : d161103 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d161103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150406, d161103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150437 q = 1) (hb : d159762 q = 1) : d161130 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d161130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150437, d161130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31732 q ha hb
  have h5 (q : Pattern) (ha : d150438 q = 1) (hb : d159762 q = 1) : d161131 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d161131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150438, d161131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150439 q = 1) (hb : d159762 q = 1) : d161132 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d161132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150439, d161132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150470 q = 1) (hb : d159762 q = 1) : d161159 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d161159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150470, d161159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31737 q ha hb
  have h8 (q : Pattern) (ha : d150471 q = 1) (hb : d159762 q = 1) : d161160 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d161160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150471, d161160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150472 q = 1) (hb : d159762 q = 1) : d161161 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d161161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150472, d161161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150473 q = 1) (hb : d159762 q = 1) : d161162 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d161162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150473, d161162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150504 q = 1) (hb : d159762 q = 1) : d161189 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d161189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150504, d161189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31742 q ha hb
  have h12 (q : Pattern) (ha : d150505 q = 1) (hb : d159762 q = 1) : d161190 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d161190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150505, d161190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150506 q = 1) (hb : d159762 q = 1) : d161191 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d161191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150506, d161191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150507 q = 1) (hb : d159762 q = 1) : d161192 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d161192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150507, d161192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150508 q = 1) (hb : d159762 q = 1) : d161193 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d161193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150508, d161193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150509 q = 1) (hb : d159762 q = 1) : d161194 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d161194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150509, d161194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro31744 (p : Pattern) (ha : d150515 p = 1) (hb : d159762 p = 1) : d161200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150510 q = 1) (hb : d159762 q = 1) : d161195 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d161195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31743 q ha hb
    | true =>
      simp only [d150510, d161195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150511 q = 1) (hb : d159762 q = 1) : d161196 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d161196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d161196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150512 q = 1) (hb : d159762 q = 1) : d161197 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d161197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d161197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150513 q = 1) (hb : d159762 q = 1) : d161198 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d161198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d161198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150514 q = 1) (hb : d159762 q = 1) : d161199 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d161199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d161199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150515 q = 1) (hb : d159762 q = 1) : d161200 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d161200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d161200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31745 (p : Pattern) (ha : d150521 p = 1) (hb : d159762 p = 1) : d161206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150516 q = 1) (hb : d159762 q = 1) : d161201 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d161201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31744 q ha hb
    | true =>
      simp only [d150516, d161201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150517 q = 1) (hb : d159762 q = 1) : d161202 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d161202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d161202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150518 q = 1) (hb : d159762 q = 1) : d161203 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d161203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d161203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150519 q = 1) (hb : d159762 q = 1) : d161204 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d161204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d161204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150520 q = 1) (hb : d159762 q = 1) : d161205 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d161205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d161205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150521 q = 1) (hb : d159762 q = 1) : d161206 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d161206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d161206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31746 (p : Pattern) (ha : d150527 p = 1) (hb : d159762 p = 1) : d161212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150522 q = 1) (hb : d159762 q = 1) : d161207 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d161207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31745 q ha hb
    | true =>
      simp only [d150522, d161207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150523 q = 1) (hb : d159762 q = 1) : d161208 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d161208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d161208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150524 q = 1) (hb : d159762 q = 1) : d161209 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d161209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d161209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150525 q = 1) (hb : d159762 q = 1) : d161210 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d161210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d161210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150526 q = 1) (hb : d159762 q = 1) : d161211 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d161211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d161211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150527 q = 1) (hb : d159762 q = 1) : d161212 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d161212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d161212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31747 (p : Pattern) (ha : d150533 p = 1) (hb : d159762 p = 1) : d161218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150528 q = 1) (hb : d159762 q = 1) : d161213 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d161213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31746 q ha hb
    | true =>
      simp only [d150528, d161213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150529 q = 1) (hb : d159762 q = 1) : d161214 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d161214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d161214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150530 q = 1) (hb : d159762 q = 1) : d161215 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150530, d161215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150530, d161215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150531 q = 1) (hb : d159762 q = 1) : d161216 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d161216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150531, d161216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150532 q = 1) (hb : d159762 q = 1) : d161217 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d161217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150532, d161217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150533 q = 1) (hb : d159762 q = 1) : d161218 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d161218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150533, d161218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31748 (p : Pattern) (ha : d150539 p = 1) (hb : d159762 p = 1) : d161224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150534 q = 1) (hb : d159762 q = 1) : d161219 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d161219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31747 q ha hb
    | true =>
      simp only [d150534, d161219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150535 q = 1) (hb : d159762 q = 1) : d161220 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d161220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d161220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150536 q = 1) (hb : d159762 q = 1) : d161221 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150536, d161221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150536, d161221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150537 q = 1) (hb : d159762 q = 1) : d161222 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d161222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150537, d161222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150538 q = 1) (hb : d159762 q = 1) : d161223 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d161223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150538, d161223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150539 q = 1) (hb : d159762 q = 1) : d161224 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d161224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150539, d161224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro31749 (p : Pattern) (ha : d150545 p = 1) (hb : d159762 p = 1) : d161230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d159762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150540 q = 1) (hb : d159762 q = 1) : d161225 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d161225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31748 q ha hb
    | true =>
      simp only [d150540, d161225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150541 q = 1) (hb : d159762 q = 1) : d161226 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d161226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d161226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150542 q = 1) (hb : d159762 q = 1) : d161227 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d161227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d161227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150543 q = 1) (hb : d159762 q = 1) : d161228 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d161228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d161228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150544 q = 1) (hb : d159762 q = 1) : d161229 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d161229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d161229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150545 q = 1) (hb : d159762 q = 1) : d161230 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d161230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d161230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
