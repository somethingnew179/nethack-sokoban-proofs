import NetHack.Soko22Hazard87.AndIntroBlocks0025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro6500 (p : Pattern) (ha : d3692 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6497 q ha hb
    | true =>
      simp only [d297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6492 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3689 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3689, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3689, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d377 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6499 q ha hb
    | true =>
      simp only [d377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6494 q ha hb
  have h9 (q : Pattern) (ha : d378 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d379 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d380 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d3691 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3691, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3691, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h13 (q : Pattern) (ha : d3692 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6501 (p : Pattern) (ha : d3698 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3693 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6498 q ha hb
    | true =>
      simp only [d3693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6500 q ha hb
  have h2 (q : Pattern) (ha : d3694 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3695 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3696 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3697 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3698 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6502 (p : Pattern) (ha : d3704 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3684 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6496 q ha hb
  have h2 (q : Pattern) (ha : d3685 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3686 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3687 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3688 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3699 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6501 q ha hb
  have h7 (q : Pattern) (ha : d3700 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3701 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3702 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3703 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3704 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6503 (p : Pattern) (ha : d512 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d485 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d511 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d511, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d512 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6504 (p : Pattern) (ha : d514 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d489 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d513 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d513, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d514 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6505 (p : Pattern) (ha : d3706 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d515 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6503 q ha hb
    | true =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6504 q ha hb
  have h4 (q : Pattern) (ha : d516 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d517 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d518 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d518, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3705 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3705, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3705, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3706 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6506 (p : Pattern) (ha : d609 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d485 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d511 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d511, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d609 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6507 (p : Pattern) (ha : d610 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d489 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d513 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d610 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6508 (p : Pattern) (ha : d3708 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d515 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6503 q ha hb
    | true =>
      simp only [d515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6504 q ha hb
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d517 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d518 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3705 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3705, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3705, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d611 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6506 q ha hb
    | true =>
      simp only [d611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6507 q ha hb
  have h9 (q : Pattern) (ha : d612 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d613 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d614 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d3707 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3707, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3707, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h13 (q : Pattern) (ha : d3708 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6509 (p : Pattern) (ha : d3714 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3709 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6505 q ha hb
    | true =>
      simp only [d3709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6508 q ha hb
  have h2 (q : Pattern) (ha : d3710 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3711 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3712 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3713 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3714 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6510 (p : Pattern) (ha : d3720 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3715 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6509 q ha hb
  have h2 (q : Pattern) (ha : d3716 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3717 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3718 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3719 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3720 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6511 (p : Pattern) (ha : d804 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d777 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d803 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d803, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d804 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6512 (p : Pattern) (ha : d806 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d781 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d805 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d805, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d806 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6513 (p : Pattern) (ha : d3723 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d807 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6511 q ha hb
    | true =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6512 q ha hb
  have h4 (q : Pattern) (ha : d808 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d809 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d810 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d810, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3722 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3722, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3722, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3723 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6514 (p : Pattern) (ha : d915 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d777 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d803 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d915 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6515 (p : Pattern) (ha : d916 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d781 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d805 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d916 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6516 (p : Pattern) (ha : d3725 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d807 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6511 q ha hb
    | true =>
      simp only [d807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6512 q ha hb
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d809 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d810 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3722 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3722, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3722, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d917 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6514 q ha hb
    | true =>
      simp only [d917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6515 q ha hb
  have h9 (q : Pattern) (ha : d918 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d919 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d920 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d3724 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3724, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3724, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h13 (q : Pattern) (ha : d3725 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6517 (p : Pattern) (ha : d3731 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3726 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6513 q ha hb
    | true =>
      simp only [d3726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6516 q ha hb
  have h2 (q : Pattern) (ha : d3727 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3728 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3729 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3730 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3731 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6518 (p : Pattern) (ha : d3737 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3732 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6517 q ha hb
  have h2 (q : Pattern) (ha : d3733 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3734 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3735 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3736 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3737 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6519 (p : Pattern) (ha : d1183 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1156 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1182 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1182, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1183 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6520 (p : Pattern) (ha : d1185 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1160 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1184 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1184, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1185 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6521 (p : Pattern) (ha : d3741 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1186 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6519 q ha hb
    | true =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6520 q ha hb
  have h4 (q : Pattern) (ha : d1187 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1188 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1189 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1189, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3740 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3740, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3740, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3741 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6522 (p : Pattern) (ha : d1326 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1156 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1182 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1326 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6523 (p : Pattern) (ha : d1327 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1184 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1327 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6524 (p : Pattern) (ha : d3743 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1186 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6519 q ha hb
    | true =>
      simp only [d1186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6520 q ha hb
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1188 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1189 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3740 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3740, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3740, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1328 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6522 q ha hb
    | true =>
      simp only [d1328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6523 q ha hb
  have h9 (q : Pattern) (ha : d1329 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1330 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1331 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d3742 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3742, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3742, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h13 (q : Pattern) (ha : d3743 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6525 (p : Pattern) (ha : d3749 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3744 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6521 q ha hb
    | true =>
      simp only [d3744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6524 q ha hb
  have h2 (q : Pattern) (ha : d3745 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3746 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3747 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3748 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3749 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6526 (p : Pattern) (ha : d3755 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3750 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6525 q ha hb
  have h2 (q : Pattern) (ha : d3751 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3752 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3753 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3754 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3755 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6527 (p : Pattern) (ha : d1644 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1617 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1643 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1643, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1644 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6528 (p : Pattern) (ha : d1646 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1621 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1645 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1645, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1646 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6529 (p : Pattern) (ha : d3760 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1647 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6527 q ha hb
    | true =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6528 q ha hb
  have h4 (q : Pattern) (ha : d1648 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1649 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1650 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1650, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3759 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3759, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3759, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3760 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6530 (p : Pattern) (ha : d1803 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1617 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1643 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1803 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6531 (p : Pattern) (ha : d1804 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1645 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1804 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6532 (p : Pattern) (ha : d3762 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1647 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6527 q ha hb
    | true =>
      simp only [d1647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6528 q ha hb
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1649 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d1650 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3759 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3759, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3759, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1805 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6530 q ha hb
    | true =>
      simp only [d1805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6531 q ha hb
  have h9 (q : Pattern) (ha : d1806 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1807 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d1808 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d3761 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3761, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3761, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h13 (q : Pattern) (ha : d3762 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6533 (p : Pattern) (ha : d3768 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3763 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6529 q ha hb
    | true =>
      simp only [d3763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6532 q ha hb
  have h2 (q : Pattern) (ha : d3764 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3765 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3766 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3767 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3768 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6534 (p : Pattern) (ha : d3774 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3769 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6533 q ha hb
  have h2 (q : Pattern) (ha : d3770 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3771 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3772 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3773 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3774 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6535 (p : Pattern) (ha : d2127 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2126 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2126, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2127 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6536 (p : Pattern) (ha : d2129 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2128 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2128, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2129 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6537 (p : Pattern) (ha : d3780 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2130 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6535 q ha hb
    | true =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6536 q ha hb
  have h4 (q : Pattern) (ha : d2131 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2132 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d2133 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2133, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3779 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3779, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3779, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3780 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6538 (p : Pattern) (ha : d2281 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2100 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2126 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2281 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6539 (p : Pattern) (ha : d2282 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2104 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2128 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2282 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6540 (p : Pattern) (ha : d3782 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2130 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6535 q ha hb
    | true =>
      simp only [d2130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6536 q ha hb
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2132 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d2133 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3779 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3779, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3779, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2283 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6538 q ha hb
    | true =>
      simp only [d2283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6539 q ha hb
  have h9 (q : Pattern) (ha : d2284 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2285 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2286 q = 1) (hb : d74045 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d74045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d3781 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3781, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3781, d74046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h13 (q : Pattern) (ha : d3782 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6541 (p : Pattern) (ha : d3788 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3783 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6537 q ha hb
    | true =>
      simp only [d3783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6540 q ha hb
  have h2 (q : Pattern) (ha : d3784 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3785 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3786 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3787 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3788 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6542 (p : Pattern) (ha : d3794 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3789 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6541 q ha hb
  have h2 (q : Pattern) (ha : d3790 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3791 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3792 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3793 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3794 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6543 (p : Pattern) (ha : d3800 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d3721 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6502 q ha hb
    | true =>
      simp only [d3721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6510 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3738 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6518 q ha hb
  have h3 (q : Pattern) (ha : d3739 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3756 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6526 q ha hb
  have h5 (q : Pattern) (ha : d3757 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3758 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3775 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6534 q ha hb
  have h8 (q : Pattern) (ha : d3776 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3777 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3778 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3795 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6542 q ha hb
  have h12 (q : Pattern) (ha : d3796 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3797 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3798 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3799 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d3800 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d3800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6544 (p : Pattern) (ha : d3806 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3801 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6543 q ha hb
    | true =>
      simp only [d3801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3802 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3803 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3804 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3805 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3806 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6545 (p : Pattern) (ha : d3812 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3807 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6544 q ha hb
    | true =>
      simp only [d3807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3808 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3809 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3810 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3811 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3812 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6546 (p : Pattern) (ha : d3818 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3813 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6545 q ha hb
    | true =>
      simp only [d3813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3814 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3815 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3816 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3817 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3818 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6547 (p : Pattern) (ha : d3824 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3819 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6546 q ha hb
    | true =>
      simp only [d3819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3820 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3821 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3822 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3823 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3824 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6548 (p : Pattern) (ha : d3830 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3825 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6547 q ha hb
    | true =>
      simp only [d3825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3826 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3827 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3828 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3829 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3830 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6549 (p : Pattern) (ha : d3836 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3831 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6548 q ha hb
    | true =>
      simp only [d3831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3832 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3833 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3834 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3835 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3836 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6550 (p : Pattern) (ha : d3842 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3837 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6549 q ha hb
    | true =>
      simp only [d3837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3838 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3839 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3840 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3841 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3842 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6551 (p : Pattern) (ha : d0 p = 1) (hb : d74046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74046 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6552 (p : Pattern) (ha : d3836 p = 1) (hb : d74047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3831 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3831, d74047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6408 q ha hb
    | true =>
      simp only [d3831, d74047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3832 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3833 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d3834 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d3835 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d3836 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro6553 (p : Pattern) (ha : d3842 p = 1) (hb : d74047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3837 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6552 q ha hb
    | true =>
      simp only [d3837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3838 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3839 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3840 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3841 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3842 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6554 (p : Pattern) (ha : d0 p = 1) (hb : d74047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74047 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6555 (p : Pattern) (ha : d4025 p = 1) (hb : d66275 p = 1) : d4025 p = 1 := by
  have h0 (q : Pattern) (ha : d4025 q = 1) (hb : d66275 q = 1) : d4025 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6556 (p : Pattern) (ha : d3845 p = 1) (hb : d52013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52010 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3843 q = 1) (hb : d52011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3843, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3843, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3844 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3844, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3845 q = 1) (hb : d52013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3845, d52013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3845, d52013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6557 (p : Pattern) (ha : d3848 p = 1) (hb : d52029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51972 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d124 q = 1) (hb : d51976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125 q = 1) (hb : d51977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d126 q = 1) (hb : d51978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52010 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3843 q = 1) (hb : d52011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3843, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3843, d52011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3844 q = 1) (hb : d52012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3844, d52012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52018 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d200 q = 1) (hb : d52020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d201 q = 1) (hb : d52021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d52022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52026 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d3846 q = 1) (hb : d52027 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3846, d52027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3846, d52027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3847 q = 1) (hb : d52028 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3847, d52028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3847, d52028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3848 q = 1) (hb : d52029 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3848, d52029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3848, d52029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6558 (p : Pattern) (ha : d3854 p = 1) (hb : d55603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3849 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3849, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6556 q ha hb
    | true =>
      simp only [d3849, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6557 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3850 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3850, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3850, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3851 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3851, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3851, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3852 q = 1) (hb : d52035 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3852, d52035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3852, d52035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55601 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3853 q = 1) (hb : d55602 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3853, d55602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3853, d55602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3854 q = 1) (hb : d55603 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3854, d55603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3854, d55603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6559 (p : Pattern) (ha : d3862 p = 1) (hb : d52143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d304 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52 q ha hb
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h3 (q : Pattern) (ha : d305 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52140 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3860 q = 1) (hb : d52141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3860, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3860, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3861 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3861, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3862 q = 1) (hb : d52143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3862, d52143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3862, d52143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6560 (p : Pattern) (ha : d3865 p = 1) (hb : d52161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d304 q = 1) (hb : d52103 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro52 q ha hb
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h3 (q : Pattern) (ha : d305 q = 1) (hb : d52104 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52140 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3860 q = 1) (hb : d52141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3860, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3860, d52141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3861 q = 1) (hb : d52142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3861, d52142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d382 q = 1) (hb : d52150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro56 q ha hb
    | true =>
      simp only [d382, d52150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h10 (q : Pattern) (ha : d383 q = 1) (hb : d52151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d383, d52151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d384 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d384, d52152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52158 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d3863 q = 1) (hb : d52159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3863, d52159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3863, d52159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3864 q = 1) (hb : d52160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3864, d52160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3864, d52160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3865 q = 1) (hb : d52161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3865, d52161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3865, d52161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6561 (p : Pattern) (ha : d3871 p = 1) (hb : d55615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3866 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3866, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6559 q ha hb
    | true =>
      simp only [d3866, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6560 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3867 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3867, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3867, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3868 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3868, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3868, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3869 q = 1) (hb : d52167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3869, d52167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3869, d52167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55613 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3870 q = 1) (hb : d55614 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3870, d55614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3870, d55614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3871 q = 1) (hb : d55615 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3871, d55615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3871, d55615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6562 (p : Pattern) (ha : d3877 p = 1) (hb : d55621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3855 q = 1) (hb : d55604 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3855, d55604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3855, d55604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6558 q ha hb
  have h3 (q : Pattern) (ha : d3856 q = 1) (hb : d55605 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3856, d55605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3856, d55605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3857 q = 1) (hb : d55606 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3857, d55606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3857, d55606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3858 q = 1) (hb : d55607 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3858, d55607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3858, d55607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3859 q = 1) (hb : d55608 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3859, d55608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3859, d55608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3872 q = 1) (hb : d55616 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3872, d55616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3872, d55616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6561 q ha hb
  have h8 (q : Pattern) (ha : d3873 q = 1) (hb : d55617 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3873, d55617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3873, d55617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3874 q = 1) (hb : d55618 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3874, d55618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3874, d55618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3875 q = 1) (hb : d55619 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3875, d55619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3875, d55619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3876 q = 1) (hb : d55620 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3876, d55620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3876, d55620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d3877 q = 1) (hb : d55621 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3877, d55621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3877, d55621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro6563 (p : Pattern) (ha : d3880 p = 1) (hb : d52315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d525 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89 q ha hb
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h3 (q : Pattern) (ha : d526 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d527 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52312 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3878 q = 1) (hb : d52313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3878, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3878, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3879 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3879, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3880 q = 1) (hb : d52315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3880, d52315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3880, d52315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6564 (p : Pattern) (ha : d3883 p = 1) (hb : d52335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52265 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d525 q = 1) (hb : d52272 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89 q ha hb
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro90 q ha hb
  have h3 (q : Pattern) (ha : d526 q = 1) (hb : d52273 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d527 q = 1) (hb : d52274 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52312 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3878 q = 1) (hb : d52313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3878, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3878, d52313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3879 q = 1) (hb : d52314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3879, d52314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52321 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d617 q = 1) (hb : d52324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro95 q ha hb
    | true =>
      simp only [d617, d52324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro96 q ha hb
  have h10 (q : Pattern) (ha : d618 q = 1) (hb : d52325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d618, d52325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d619 q = 1) (hb : d52326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d619, d52326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52332 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d3881 q = 1) (hb : d52333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3881, d52333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3881, d52333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3882 q = 1) (hb : d52334 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3882, d52334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3882, d52334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3883 q = 1) (hb : d52335 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3883, d52335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3883, d52335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6565 (p : Pattern) (ha : d3889 p = 1) (hb : d55628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3884 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3884, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6563 q ha hb
    | true =>
      simp only [d3884, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6564 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3885 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3885, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3885, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3886 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3886, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3886, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3887 q = 1) (hb : d52352 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3887, d52352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3887, d52352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55626 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3888 q = 1) (hb : d55627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3888, d55627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3888, d55627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3889 q = 1) (hb : d55628 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3889, d55628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3889, d55628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6566 (p : Pattern) (ha : d3895 p = 1) (hb : d55634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3890 q = 1) (hb : d55629 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3890, d55629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3890, d55629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6565 q ha hb
  have h2 (q : Pattern) (ha : d3891 q = 1) (hb : d55630 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3891, d55630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3891, d55630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3892 q = 1) (hb : d55631 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3892, d55631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3892, d55631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3893 q = 1) (hb : d55632 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3893, d55632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3893, d55632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3894 q = 1) (hb : d55633 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3894, d55633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3894, d55633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3895 q = 1) (hb : d55634 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3895, d55634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3895, d55634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6567 (p : Pattern) (ha : d3899 p = 1) (hb : d52536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d817 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro136 q ha hb
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h3 (q : Pattern) (ha : d818 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d819 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52533 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3897 q = 1) (hb : d52534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3897, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3897, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3898 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3898, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3899 q = 1) (hb : d52536 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3899, d52536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3899, d52536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6568 (p : Pattern) (ha : d3902 p = 1) (hb : d52556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52487 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d817 q = 1) (hb : d52494 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro136 q ha hb
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro137 q ha hb
  have h3 (q : Pattern) (ha : d818 q = 1) (hb : d52495 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d819 q = 1) (hb : d52496 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52533 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3897 q = 1) (hb : d52534 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3897, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3897, d52534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3898 q = 1) (hb : d52535 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3898, d52535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52542 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d923 q = 1) (hb : d52545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro142 q ha hb
    | true =>
      simp only [d923, d52545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro143 q ha hb
  have h10 (q : Pattern) (ha : d924 q = 1) (hb : d52546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d924, d52546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d925 q = 1) (hb : d52547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d925, d52547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52553 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d3900 q = 1) (hb : d52554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3900, d52554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3900, d52554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3901 q = 1) (hb : d52555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3901, d52555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3901, d52555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3902 q = 1) (hb : d52556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3902, d52556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3902, d52556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6569 (p : Pattern) (ha : d3908 p = 1) (hb : d55642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3903 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3903, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6567 q ha hb
    | true =>
      simp only [d3903, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6568 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3904 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3904, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3904, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3905 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3905, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3905, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3906 q = 1) (hb : d52573 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3906, d52573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3906, d52573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55640 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3907 q = 1) (hb : d55641 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3907, d55641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3907, d55641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3908 q = 1) (hb : d55642 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3908, d55642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3908, d55642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6570 (p : Pattern) (ha : d3914 p = 1) (hb : d55648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3909 q = 1) (hb : d55643 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3909, d55643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3909, d55643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6569 q ha hb
  have h2 (q : Pattern) (ha : d3910 q = 1) (hb : d55644 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3910, d55644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3910, d55644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3911 q = 1) (hb : d55645 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3911, d55645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3911, d55645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3912 q = 1) (hb : d55646 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3912, d55646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3912, d55646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3913 q = 1) (hb : d55647 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3913, d55647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3913, d55647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3914 q = 1) (hb : d55648 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3914, d55648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3914, d55648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6571 (p : Pattern) (ha : d3919 p = 1) (hb : d52816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1196 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro188 q ha hb
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h3 (q : Pattern) (ha : d1197 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1198 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52813 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3917 q = 1) (hb : d52814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3917, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3917, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3918 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3918, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3919 q = 1) (hb : d52816 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3919, d52816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3919, d52816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6572 (p : Pattern) (ha : d3922 p = 1) (hb : d52836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52770 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1196 q = 1) (hb : d52777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro188 q ha hb
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q ha hb
  have h3 (q : Pattern) (ha : d1197 q = 1) (hb : d52778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1198 q = 1) (hb : d52779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52813 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3917 q = 1) (hb : d52814 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3917, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3917, d52814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3918 q = 1) (hb : d52815 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3918, d52815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52822 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1334 q = 1) (hb : d52825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro194 q ha hb
    | true =>
      simp only [d1334, d52825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q ha hb
  have h10 (q : Pattern) (ha : d1335 q = 1) (hb : d52826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1335, d52826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1336 q = 1) (hb : d52827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1336, d52827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52833 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d3920 q = 1) (hb : d52834 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3920, d52834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3920, d52834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3921 q = 1) (hb : d52835 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3921, d52835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3921, d52835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3922 q = 1) (hb : d52836 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3922, d52836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3922, d52836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6573 (p : Pattern) (ha : d3928 p = 1) (hb : d55657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3923 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3923, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6571 q ha hb
    | true =>
      simp only [d3923, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3924 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3924, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3924, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3925 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3925, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3925, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3926 q = 1) (hb : d52853 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3926, d52853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3926, d52853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55655 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3927 q = 1) (hb : d55656 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3927, d55656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3927, d55656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3928 q = 1) (hb : d55657 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3928, d55657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3928, d55657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6574 (p : Pattern) (ha : d3934 p = 1) (hb : d55663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3929 q = 1) (hb : d55658 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3929, d55658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3929, d55658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6573 q ha hb
  have h2 (q : Pattern) (ha : d3930 q = 1) (hb : d55659 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3930, d55659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3930, d55659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3931 q = 1) (hb : d55660 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3931, d55660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3931, d55660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3932 q = 1) (hb : d55661 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3932, d55661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3932, d55661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3933 q = 1) (hb : d55662 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3933, d55662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3933, d55662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3934 q = 1) (hb : d55663 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3934, d55663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3934, d55663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6575 (p : Pattern) (ha : d3940 p = 1) (hb : d53131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1657 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro244 q ha hb
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h3 (q : Pattern) (ha : d1658 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1659 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53128 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3938 q = 1) (hb : d53129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3938, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3938, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3939 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3939, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3939, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3940 q = 1) (hb : d53131 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3940, d53131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3940, d53131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6576 (p : Pattern) (ha : d3943 p = 1) (hb : d53151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53091 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1657 q = 1) (hb : d53098 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro244 q ha hb
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q ha hb
  have h3 (q : Pattern) (ha : d1658 q = 1) (hb : d53099 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1659 q = 1) (hb : d53100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53128 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3938 q = 1) (hb : d53129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3938, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3938, d53129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3939 q = 1) (hb : d53130 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3939, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3939, d53130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53137 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1811 q = 1) (hb : d53140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro250 q ha hb
    | true =>
      simp only [d1811, d53140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q ha hb
  have h10 (q : Pattern) (ha : d1812 q = 1) (hb : d53141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1812, d53141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1813 q = 1) (hb : d53142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1813, d53142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53148 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d3941 q = 1) (hb : d53149 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3941, d53149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3941, d53149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3942 q = 1) (hb : d53150 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3942, d53150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3942, d53150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3943 q = 1) (hb : d53151 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3943, d53151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3943, d53151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6577 (p : Pattern) (ha : d3949 p = 1) (hb : d55673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3944 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3944, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6575 q ha hb
    | true =>
      simp only [d3944, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6576 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3945 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3945, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3945, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3946 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3946, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3946, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3947 q = 1) (hb : d53168 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3947, d53168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3947, d53168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55671 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3948 q = 1) (hb : d55672 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3948, d55672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3948, d55672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3949 q = 1) (hb : d55673 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3949, d55673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3949, d55673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6578 (p : Pattern) (ha : d3955 p = 1) (hb : d55679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3950 q = 1) (hb : d55674 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3950, d55674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3950, d55674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6577 q ha hb
  have h2 (q : Pattern) (ha : d3951 q = 1) (hb : d55675 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3951, d55675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3951, d55675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3952 q = 1) (hb : d55676 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3952, d55676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3952, d55676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3953 q = 1) (hb : d55677 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3953, d55677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3953, d55677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3954 q = 1) (hb : d55678 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3954, d55678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3954, d55678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3955 q = 1) (hb : d55679 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3955, d55679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3955, d55679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6579 (p : Pattern) (ha : d3962 p = 1) (hb : d53448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h3 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53445 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3960 q = 1) (hb : d53446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3960, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3960, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3961 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3961, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3961, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3962 q = 1) (hb : d53448 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3962, d53448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3962, d53448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6580 (p : Pattern) (ha : d3965 p = 1) (hb : d53468 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2140 q = 1) (hb : d53419 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro303 q ha hb
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q ha hb
  have h3 (q : Pattern) (ha : d2141 q = 1) (hb : d53420 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2142 q = 1) (hb : d53421 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53445 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3960 q = 1) (hb : d53446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3960, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3960, d53446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3961 q = 1) (hb : d53447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3961, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3961, d53447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53454 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2289 q = 1) (hb : d53457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro309 q ha hb
    | true =>
      simp only [d2289, d53457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q ha hb
  have h10 (q : Pattern) (ha : d2290 q = 1) (hb : d53458 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2290, d53458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2291 q = 1) (hb : d53459 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2291, d53459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53465 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d3963 q = 1) (hb : d53466 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3963, d53466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d3963, d53466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3964 q = 1) (hb : d53467 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3964, d53467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3964, d53467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3965 q = 1) (hb : d53468 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3965, d53468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3965, d53468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro6581 (p : Pattern) (ha : d3971 p = 1) (hb : d55690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3966 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3966, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6579 q ha hb
    | true =>
      simp only [d3966, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6580 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3967 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3967, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3967, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3968 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3968, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3968, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3969 q = 1) (hb : d53485 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3969, d53485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3969, d53485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55688 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3970 q = 1) (hb : d55689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3970, d55689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3970, d55689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3971 q = 1) (hb : d55690 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3971, d55690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3971, d55690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6582 (p : Pattern) (ha : d3977 p = 1) (hb : d55696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3972 q = 1) (hb : d55691 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3972, d55691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3972, d55691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6581 q ha hb
  have h2 (q : Pattern) (ha : d3973 q = 1) (hb : d55692 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3973, d55692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3973, d55692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3974 q = 1) (hb : d55693 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3974, d55693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3974, d55693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3975 q = 1) (hb : d55694 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3975, d55694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3975, d55694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3976 q = 1) (hb : d55695 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3976, d55695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3976, d55695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3977 q = 1) (hb : d55696 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3977, d55696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3977, d55696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6583 (p : Pattern) (ha : d3983 p = 1) (hb : d55702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d3896 q = 1) (hb : d55635 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3896, d55635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6562 q ha hb
    | true =>
      simp only [d3896, d55635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6566 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3915 q = 1) (hb : d55649 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3915, d55649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3915, d55649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6570 q ha hb
  have h3 (q : Pattern) (ha : d3916 q = 1) (hb : d55650 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3916, d55650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3916, d55650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3935 q = 1) (hb : d55664 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3935, d55664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3935, d55664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6574 q ha hb
  have h5 (q : Pattern) (ha : d3936 q = 1) (hb : d55665 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3936, d55665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3936, d55665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3937 q = 1) (hb : d55666 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3937, d55666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3937, d55666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3956 q = 1) (hb : d55680 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3956, d55680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3956, d55680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6578 q ha hb
  have h8 (q : Pattern) (ha : d3957 q = 1) (hb : d55681 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3957, d55681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3957, d55681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3958 q = 1) (hb : d55682 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3958, d55682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3958, d55682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3959 q = 1) (hb : d55683 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3959, d55683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3959, d55683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3978 q = 1) (hb : d55697 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3978, d55697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3978, d55697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6582 q ha hb
  have h12 (q : Pattern) (ha : d3979 q = 1) (hb : d55698 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3979, d55698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3979, d55698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3980 q = 1) (hb : d55699 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3980, d55699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3980, d55699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3981 q = 1) (hb : d55700 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3981, d55700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3981, d55700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3982 q = 1) (hb : d55701 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3982, d55701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3982, d55701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d3983 q = 1) (hb : d55702 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3983, d55702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d3983, d55702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6584 (p : Pattern) (ha : d3989 p = 1) (hb : d55708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3984 q = 1) (hb : d55703 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3984, d55703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6583 q ha hb
    | true =>
      simp only [d3984, d55703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3985 q = 1) (hb : d55704 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3985, d55704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3985, d55704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3986 q = 1) (hb : d55705 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3986, d55705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3986, d55705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3987 q = 1) (hb : d55706 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3987, d55706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3987, d55706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3988 q = 1) (hb : d55707 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3988, d55707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3988, d55707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3989 q = 1) (hb : d55708 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3989, d55708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3989, d55708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6585 (p : Pattern) (ha : d3995 p = 1) (hb : d55714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3990 q = 1) (hb : d55709 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3990, d55709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6584 q ha hb
    | true =>
      simp only [d3990, d55709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3991 q = 1) (hb : d55710 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3991, d55710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3991, d55710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3992 q = 1) (hb : d55711 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3992, d55711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3992, d55711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3993 q = 1) (hb : d55712 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3993, d55712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3993, d55712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3994 q = 1) (hb : d55713 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3994, d55713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3994, d55713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3995 q = 1) (hb : d55714 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3995, d55714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3995, d55714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6586 (p : Pattern) (ha : d4001 p = 1) (hb : d55720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3996 q = 1) (hb : d55715 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3996, d55715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6585 q ha hb
    | true =>
      simp only [d3996, d55715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3997 q = 1) (hb : d55716 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3997, d55716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3997, d55716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3998 q = 1) (hb : d55717 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3998, d55717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3998, d55717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3999 q = 1) (hb : d55718 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3999, d55718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3999, d55718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4000 q = 1) (hb : d55719 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4000, d55719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4000, d55719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4001 q = 1) (hb : d55720 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4001, d55720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4001, d55720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6587 (p : Pattern) (ha : d4007 p = 1) (hb : d55726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4002 q = 1) (hb : d55721 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4002, d55721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6586 q ha hb
    | true =>
      simp only [d4002, d55721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4003 q = 1) (hb : d55722 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4003, d55722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4003, d55722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4004 q = 1) (hb : d55723 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4004, d55723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4004, d55723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4005 q = 1) (hb : d55724 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4005, d55724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4005, d55724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4006 q = 1) (hb : d55725 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4006, d55725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4006, d55725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4007 q = 1) (hb : d55726 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4007, d55726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4007, d55726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6588 (p : Pattern) (ha : d4013 p = 1) (hb : d55732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4008 q = 1) (hb : d55727 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4008, d55727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6587 q ha hb
    | true =>
      simp only [d4008, d55727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4009 q = 1) (hb : d55728 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4009, d55728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4009, d55728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4010 q = 1) (hb : d55729 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4010, d55729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4010, d55729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4011 q = 1) (hb : d55730 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4011, d55730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4011, d55730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4012 q = 1) (hb : d55731 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4012, d55731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4012, d55731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4013 q = 1) (hb : d55732 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4013, d55732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4013, d55732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6589 (p : Pattern) (ha : d4019 p = 1) (hb : d55738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4014 q = 1) (hb : d55733 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4014, d55733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6588 q ha hb
    | true =>
      simp only [d4014, d55733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4015 q = 1) (hb : d55734 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4015, d55734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4015, d55734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4016 q = 1) (hb : d55735 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4016, d55735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4016, d55735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4017 q = 1) (hb : d55736 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4017, d55736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4017, d55736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4018 q = 1) (hb : d55737 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4018, d55737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4018, d55737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4019 q = 1) (hb : d55738 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4019, d55738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4019, d55738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6590 (p : Pattern) (ha : d4025 p = 1) (hb : d55744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4020 q = 1) (hb : d55739 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4020, d55739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6589 q ha hb
    | true =>
      simp only [d4020, d55739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4021 q = 1) (hb : d55740 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4021, d55740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4021, d55740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4022 q = 1) (hb : d55741 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4022, d55741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4022, d55741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4023 q = 1) (hb : d55742 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4023, d55742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4023, d55742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4024 q = 1) (hb : d55743 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4024, d55743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4024, d55743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4025 q = 1) (hb : d55744 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4025, d55744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4025, d55744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6591 (p : Pattern) (ha : d0 p = 1) (hb : d66275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66275 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6592 (p : Pattern) (ha : d4019 p = 1) (hb : d56775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4016 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4017 q = 1) (hb : d56775 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4017, d56775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d4017, d56775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d56775 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d4018 q = 1) (hb : d56775 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4019 q = 1) (hb : d56775 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6593 (p : Pattern) (ha : d4025 p = 1) (hb : d56776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56775 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4020 q = 1) (hb : d56775 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6592 q ha hb
    | true =>
      simp only [d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4021 q = 1) (hb : d56776 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4021, d56776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4021, d56776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d56776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4022 q = 1) (hb : d56776 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4023 q = 1) (hb : d56776 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d4024 q = 1) (hb : d56776 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d4025 q = 1) (hb : d56776 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro6594 (p : Pattern) (ha : d0 p = 1) (hb : d56776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56776 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6595 (p : Pattern) (ha : d123 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d39 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d122 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d123 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6596 (p : Pattern) (ha : d3845 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d124 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6595 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d126 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3843 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3843, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3843, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3844 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3845 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6597 (p : Pattern) (ha : d199 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d39 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d121 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d199 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6598 (p : Pattern) (ha : d3848 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d124 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6595 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d126 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3843 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3843, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3843, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3844 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6597 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d201 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3846 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3846, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3846, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3847 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3848 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6599 (p : Pattern) (ha : d3854 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3849 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6596 q ha hb
    | true =>
      simp only [d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6598 q ha hb
  have h2 (q : Pattern) (ha : d3850 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3851 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3852 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3853 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3854 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6600 (p : Pattern) (ha : d303 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d301 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d301, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d302 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d303 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6601 (p : Pattern) (ha : d3862 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d304 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6600 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6595 q ha hb
  have h3 (q : Pattern) (ha : d305 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3860 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3860, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3860, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3861 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3862 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6602 (p : Pattern) (ha : d381 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d301 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d302 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d381 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6603 (p : Pattern) (ha : d3865 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d304 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6600 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6595 q ha hb
  have h3 (q : Pattern) (ha : d305 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3860 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3860, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3860, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3861 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d382 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6602 q ha hb
    | true =>
      simp only [d382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6597 q ha hb
  have h9 (q : Pattern) (ha : d383 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d384 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3863 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3863, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3863, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3864 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3865 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6604 (p : Pattern) (ha : d3871 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3866 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6601 q ha hb
    | true =>
      simp only [d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6603 q ha hb
  have h2 (q : Pattern) (ha : d3867 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3868 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3869 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3870 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3871 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6605 (p : Pattern) (ha : d3877 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3855 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6599 q ha hb
  have h2 (q : Pattern) (ha : d3856 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3857 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3858 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3859 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3872 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6604 q ha hb
  have h7 (q : Pattern) (ha : d3873 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3874 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3875 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3876 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3877 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6606 (p : Pattern) (ha : d521 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d484 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d519 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d519, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d520 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d521 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6607 (p : Pattern) (ha : d524 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d488 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d522 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d522, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d523 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d524 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6608 (p : Pattern) (ha : d3880 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d525 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6606 q ha hb
    | true =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6607 q ha hb
  have h3 (q : Pattern) (ha : d526 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d527 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3878 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3878, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3878, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3879 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3880 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6609 (p : Pattern) (ha : d615 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d484 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d519 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d520 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d615 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6610 (p : Pattern) (ha : d616 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d522 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d523 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d616 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6611 (p : Pattern) (ha : d3883 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d525 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6606 q ha hb
    | true =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6607 q ha hb
  have h3 (q : Pattern) (ha : d526 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d527 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3878 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3878, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3878, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3879 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d617 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6609 q ha hb
    | true =>
      simp only [d617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6610 q ha hb
  have h9 (q : Pattern) (ha : d618 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d619 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3881 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3881, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3881, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3882 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3883 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6612 (p : Pattern) (ha : d3889 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3884 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6608 q ha hb
    | true =>
      simp only [d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6611 q ha hb
  have h2 (q : Pattern) (ha : d3885 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3886 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3887 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3888 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3889 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6613 (p : Pattern) (ha : d3895 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3890 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6612 q ha hb
  have h2 (q : Pattern) (ha : d3891 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3892 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3893 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3894 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3895 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6614 (p : Pattern) (ha : d813 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d811 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d811, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d812 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d813 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6615 (p : Pattern) (ha : d816 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d780 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d814 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d814, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d815 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d816 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6616 (p : Pattern) (ha : d3899 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d817 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6614 q ha hb
    | true =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6615 q ha hb
  have h3 (q : Pattern) (ha : d818 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d819 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3897 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3897, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3897, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3898 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3899 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6617 (p : Pattern) (ha : d921 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d811 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d812 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d921 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6618 (p : Pattern) (ha : d922 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d814 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d815 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d922 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6619 (p : Pattern) (ha : d3902 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d817 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6614 q ha hb
    | true =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6615 q ha hb
  have h3 (q : Pattern) (ha : d818 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d819 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3897 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3897, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3897, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3898 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d923 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6617 q ha hb
    | true =>
      simp only [d923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6618 q ha hb
  have h9 (q : Pattern) (ha : d924 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d925 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3900 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3900, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3900, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3901 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3902 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6620 (p : Pattern) (ha : d3908 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3903 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6616 q ha hb
    | true =>
      simp only [d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6619 q ha hb
  have h2 (q : Pattern) (ha : d3904 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3905 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3906 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3907 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3908 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6621 (p : Pattern) (ha : d3914 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3909 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6620 q ha hb
  have h2 (q : Pattern) (ha : d3910 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3911 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3912 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3913 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3914 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6622 (p : Pattern) (ha : d1192 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1190 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1190, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1191 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1192 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6623 (p : Pattern) (ha : d1195 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1193 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1193, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1194 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1195 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6624 (p : Pattern) (ha : d3919 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1196 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6622 q ha hb
    | true =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6623 q ha hb
  have h3 (q : Pattern) (ha : d1197 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1198 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3917 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3917, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3917, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3918 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3919 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6625 (p : Pattern) (ha : d1332 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1155 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1190 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1191 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1332 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6626 (p : Pattern) (ha : d1333 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1193 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1194 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1333 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6627 (p : Pattern) (ha : d3922 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1196 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6622 q ha hb
    | true =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6623 q ha hb
  have h3 (q : Pattern) (ha : d1197 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1198 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3917 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3917, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3917, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3918 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1334 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6625 q ha hb
    | true =>
      simp only [d1334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6626 q ha hb
  have h9 (q : Pattern) (ha : d1335 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1336 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3920 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3920, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3920, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3921 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3922 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6628 (p : Pattern) (ha : d3928 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3923 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6624 q ha hb
    | true =>
      simp only [d3923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6627 q ha hb
  have h2 (q : Pattern) (ha : d3924 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3925 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3926 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3927 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3928 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6629 (p : Pattern) (ha : d3934 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3929 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6628 q ha hb
  have h2 (q : Pattern) (ha : d3930 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3931 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3932 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3933 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3934 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6630 (p : Pattern) (ha : d1653 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1616 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1651 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1651, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1652 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1653 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6631 (p : Pattern) (ha : d1656 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1654 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1654, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1655 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1656 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6632 (p : Pattern) (ha : d3940 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1657 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6630 q ha hb
    | true =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6631 q ha hb
  have h3 (q : Pattern) (ha : d1658 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1659 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3938 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3938, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3938, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3939 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3940 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6633 (p : Pattern) (ha : d1809 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1616 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1651 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1652 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1809 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6634 (p : Pattern) (ha : d1810 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1654 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1655 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1810 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6635 (p : Pattern) (ha : d3943 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1657 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6630 q ha hb
    | true =>
      simp only [d1657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6631 q ha hb
  have h3 (q : Pattern) (ha : d1658 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1659 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3938 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3938, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3938, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3939 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1811 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6633 q ha hb
    | true =>
      simp only [d1811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6634 q ha hb
  have h9 (q : Pattern) (ha : d1812 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1813 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3941 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3941, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3941, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3942 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3943 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6636 (p : Pattern) (ha : d3949 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3944 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6632 q ha hb
    | true =>
      simp only [d3944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6635 q ha hb
  have h2 (q : Pattern) (ha : d3945 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3946 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3947 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3948 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3949 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6637 (p : Pattern) (ha : d3955 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3950 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6636 q ha hb
  have h2 (q : Pattern) (ha : d3951 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3952 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3953 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3954 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3955 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6638 (p : Pattern) (ha : d2136 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2099 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2134 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2134, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2135 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2136 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6639 (p : Pattern) (ha : d2139 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2103 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2137 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2137, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2138 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2139 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6640 (p : Pattern) (ha : d3962 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2140 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6638 q ha hb
    | true =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6639 q ha hb
  have h3 (q : Pattern) (ha : d2141 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2142 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3960 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3960, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3960, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3961 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3962 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro6641 (p : Pattern) (ha : d2287 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2134 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2135 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2287 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6642 (p : Pattern) (ha : d2288 p = 1) (hb : d66277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2103 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2137 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2138 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2288 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro6643 (p : Pattern) (ha : d3965 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2140 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6638 q ha hb
    | true =>
      simp only [d2140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6639 q ha hb
  have h3 (q : Pattern) (ha : d2141 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2142 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3960 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3960, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3960, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3961 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2289 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6641 q ha hb
    | true =>
      simp only [d2289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6642 q ha hb
  have h9 (q : Pattern) (ha : d2290 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2291 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3963 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3963, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3963, d74048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3964 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3965 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6644 (p : Pattern) (ha : d3971 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3966 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6640 q ha hb
    | true =>
      simp only [d3966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6643 q ha hb
  have h2 (q : Pattern) (ha : d3967 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3968 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3969 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3970 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3971 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6645 (p : Pattern) (ha : d3977 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3972 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6644 q ha hb
  have h2 (q : Pattern) (ha : d3973 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3974 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3975 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3976 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3977 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6646 (p : Pattern) (ha : d3983 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d3896 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6605 q ha hb
    | true =>
      simp only [d3896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6613 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3915 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6621 q ha hb
  have h3 (q : Pattern) (ha : d3916 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3935 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6629 q ha hb
  have h5 (q : Pattern) (ha : d3936 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3937 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3956 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6637 q ha hb
  have h8 (q : Pattern) (ha : d3957 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3958 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3959 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3978 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6645 q ha hb
  have h12 (q : Pattern) (ha : d3979 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3980 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3981 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3982 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d3983 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d3983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6647 (p : Pattern) (ha : d3989 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3984 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6646 q ha hb
    | true =>
      simp only [d3984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3985 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3986 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3987 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3988 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3989 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6648 (p : Pattern) (ha : d3995 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3990 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6647 q ha hb
    | true =>
      simp only [d3990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3991 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3992 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3993 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3994 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3995 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6649 (p : Pattern) (ha : d4001 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3996 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6648 q ha hb
    | true =>
      simp only [d3996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3997 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3998 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3999 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4000 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4001 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6650 (p : Pattern) (ha : d4007 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4002 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6649 q ha hb
    | true =>
      simp only [d4002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4003 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4004 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4005 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4006 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4007 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6651 (p : Pattern) (ha : d4013 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4008 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6650 q ha hb
    | true =>
      simp only [d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4009 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4010 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4011 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4012 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4013 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6652 (p : Pattern) (ha : d4019 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4014 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6651 q ha hb
    | true =>
      simp only [d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4015 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4016 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4017 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4018 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4019 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6653 (p : Pattern) (ha : d4025 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4020 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6652 q ha hb
    | true =>
      simp only [d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4021 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4022 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4023 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4024 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4025 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6654 (p : Pattern) (ha : d0 p = 1) (hb : d74048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6655 (p : Pattern) (ha : d4025 p = 1) (hb : d74052 p = 1) : d4025 p = 1 := by
  have h0 (q : Pattern) (ha : d4025 q = 1) (hb : d74052 q = 1) : d4025 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6656 (p : Pattern) (ha : d1 p = 1) (hb : d4025 p = 1) : d4025 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d4025 q = 1) : d4025 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro6657 (p : Pattern) (ha : d0 p = 1) (hb : d74052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74052 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6658 (p : Pattern) (ha : d3845 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3843 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3844 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3844, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d3845 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6659 (p : Pattern) (ha : d3848 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d3843 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3844 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3844, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3846 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3847 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3847, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3847, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d3848 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6660 (p : Pattern) (ha : d3854 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3849 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6658 q ha hb
    | true =>
      simp only [d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6659 q ha hb
  have h2 (q : Pattern) (ha : d3850 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3851 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3852 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3853 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3854 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6661 (p : Pattern) (ha : d3862 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3860 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3861 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3861, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d3862 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6662 (p : Pattern) (ha : d3865 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d3860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3861 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3861, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3863 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3864 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3864, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3864, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d3865 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6663 (p : Pattern) (ha : d3871 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3866 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6661 q ha hb
    | true =>
      simp only [d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6662 q ha hb
  have h2 (q : Pattern) (ha : d3867 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3868 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3869 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3870 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3871 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6664 (p : Pattern) (ha : d3877 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3855 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6660 q ha hb
  have h2 (q : Pattern) (ha : d3856 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3857 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3858 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3859 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3872 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6663 q ha hb
  have h7 (q : Pattern) (ha : d3873 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3874 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3875 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3876 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3877 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6665 (p : Pattern) (ha : d3880 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3879 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3879, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d3880 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6666 (p : Pattern) (ha : d3883 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d3878 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3879 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3879, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3881 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3882 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3882, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3882, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d3883 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6667 (p : Pattern) (ha : d3889 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3884 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6665 q ha hb
    | true =>
      simp only [d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6666 q ha hb
  have h2 (q : Pattern) (ha : d3885 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3886 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3887 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3888 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3889 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6668 (p : Pattern) (ha : d3895 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3890 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6667 q ha hb
  have h2 (q : Pattern) (ha : d3891 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3892 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3893 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3894 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3895 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6669 (p : Pattern) (ha : d3899 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3897 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3898 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3898, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d3899 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6670 (p : Pattern) (ha : d3902 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d3897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3898 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3898, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3900 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3901 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3901, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3901, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d3902 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6671 (p : Pattern) (ha : d3908 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3903 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6669 q ha hb
    | true =>
      simp only [d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6670 q ha hb
  have h2 (q : Pattern) (ha : d3904 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3905 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3906 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3907 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3908 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6672 (p : Pattern) (ha : d3914 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3909 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6671 q ha hb
  have h2 (q : Pattern) (ha : d3910 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3911 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3912 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3913 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3914 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6673 (p : Pattern) (ha : d3919 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3918 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3918, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d3919 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6674 (p : Pattern) (ha : d3922 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d3917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3918 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3918, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3920 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3921 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3921, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3921, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d3922 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6675 (p : Pattern) (ha : d3928 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3923 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6673 q ha hb
    | true =>
      simp only [d3923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6674 q ha hb
  have h2 (q : Pattern) (ha : d3924 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3925 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3926 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3927 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3928 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6676 (p : Pattern) (ha : d3934 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3929 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6675 q ha hb
  have h2 (q : Pattern) (ha : d3930 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3931 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3932 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3933 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3934 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6677 (p : Pattern) (ha : d3940 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3938 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3939 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3939, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3939, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d3940 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6678 (p : Pattern) (ha : d3943 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d3938 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3939 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3939, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3939, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3941 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3942 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3942, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3942, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d3943 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6679 (p : Pattern) (ha : d3949 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3944 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6677 q ha hb
    | true =>
      simp only [d3944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6678 q ha hb
  have h2 (q : Pattern) (ha : d3945 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3946 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3947 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3948 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3949 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6680 (p : Pattern) (ha : d3955 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3950 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6679 q ha hb
  have h2 (q : Pattern) (ha : d3951 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3952 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3953 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3954 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3955 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6681 (p : Pattern) (ha : d3962 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d3960 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3961 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3961, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3961, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d3962 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro6682 (p : Pattern) (ha : d3965 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d56773 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d3960 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3961 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3961, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3961, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d3963 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d3964 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3964, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3964, d66089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d3965 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h5 p ha hb
theorem andIntro6683 (p : Pattern) (ha : d3971 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3966 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6681 q ha hb
    | true =>
      simp only [d3966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6682 q ha hb
  have h2 (q : Pattern) (ha : d3967 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3968 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3969 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3970 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3971 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6684 (p : Pattern) (ha : d3977 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3972 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6683 q ha hb
  have h2 (q : Pattern) (ha : d3973 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3974 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3975 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3976 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3977 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6685 (p : Pattern) (ha : d3983 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d3896 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6664 q ha hb
    | true =>
      simp only [d3896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6668 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3915 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6672 q ha hb
  have h3 (q : Pattern) (ha : d3916 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3935 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6676 q ha hb
  have h5 (q : Pattern) (ha : d3936 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3937 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3956 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6680 q ha hb
  have h8 (q : Pattern) (ha : d3957 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3958 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3959 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3978 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6684 q ha hb
  have h12 (q : Pattern) (ha : d3979 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3980 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3981 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3982 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d3983 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d3983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6686 (p : Pattern) (ha : d3989 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3984 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6685 q ha hb
    | true =>
      simp only [d3984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3985 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3986 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3987 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3988 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3989 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6687 (p : Pattern) (ha : d3995 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3990 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6686 q ha hb
    | true =>
      simp only [d3990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3991 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3992 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3993 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3994 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3995 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6688 (p : Pattern) (ha : d4001 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3996 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6687 q ha hb
    | true =>
      simp only [d3996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3997 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3998 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3999 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4000 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4001 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6689 (p : Pattern) (ha : d4007 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4002 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6688 q ha hb
    | true =>
      simp only [d4002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4003 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4004 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4005 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4006 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4007 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6690 (p : Pattern) (ha : d4013 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4008 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6689 q ha hb
    | true =>
      simp only [d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4009 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4010 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4011 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4012 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4013 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6691 (p : Pattern) (ha : d4019 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4014 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6690 q ha hb
    | true =>
      simp only [d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4015 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4016 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4017 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4018 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4019 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6692 (p : Pattern) (ha : d4025 p = 1) (hb : d66089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4020 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6691 q ha hb
    | true =>
      simp only [d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4021 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4022 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4023 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4024 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4025 q = 1) (hb : d66089 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6693 (p : Pattern) (ha : d4025 p = 1) (hb : d66091 p = 1) : d4025 p = 1 := by
  have h0 (q : Pattern) (ha : d4025 q = 1) (hb : d66091 q = 1) : d4025 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6694 (p : Pattern) (ha : d3854 p = 1) (hb : d55898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55895 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3849 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3849, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6556 q ha hb
    | true =>
      simp only [d3849, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6557 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3850 q = 1) (hb : d52033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3850, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3850, d52033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3851 q = 1) (hb : d52034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3851, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3851, d52034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3852 q = 1) (hb : d55896 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3852, d55896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3852, d55896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55601 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3853 q = 1) (hb : d55897 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3853, d55897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3853, d55897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3854 q = 1) (hb : d55898 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3854, d55898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3854, d55898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6695 (p : Pattern) (ha : d3871 p = 1) (hb : d55907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55904 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3866 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3866, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6559 q ha hb
    | true =>
      simp only [d3866, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6560 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3867 q = 1) (hb : d52165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3867, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3867, d52165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3868 q = 1) (hb : d52166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3868, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3868, d52166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3869 q = 1) (hb : d55905 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3869, d55905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3869, d55905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55613 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3870 q = 1) (hb : d55906 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3870, d55906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3870, d55906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3871 q = 1) (hb : d55907 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3871, d55907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3871, d55907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6696 (p : Pattern) (ha : d3877 p = 1) (hb : d55913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d54637 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3855 q = 1) (hb : d55899 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3855, d55899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3855, d55899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6694 q ha hb
  have h3 (q : Pattern) (ha : d3856 q = 1) (hb : d55900 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3856, d55900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3856, d55900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3857 q = 1) (hb : d55901 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3857, d55901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3857, d55901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3858 q = 1) (hb : d55902 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3858, d55902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3858, d55902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3859 q = 1) (hb : d55903 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3859, d55903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3859, d55903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3872 q = 1) (hb : d55908 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3872, d55908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3872, d55908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6695 q ha hb
  have h8 (q : Pattern) (ha : d3873 q = 1) (hb : d55909 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3873, d55909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3873, d55909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3874 q = 1) (hb : d55910 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3874, d55910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3874, d55910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3875 q = 1) (hb : d55911 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3875, d55911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3875, d55911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3876 q = 1) (hb : d55912 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3876, d55912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3876, d55912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d3877 q = 1) (hb : d55913 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3877, d55913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3877, d55913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro6697 (p : Pattern) (ha : d3889 p = 1) (hb : d55917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55914 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3884 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3884, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6563 q ha hb
    | true =>
      simp only [d3884, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6564 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3885 q = 1) (hb : d52350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3885, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3885, d52350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3886 q = 1) (hb : d52351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3886, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3886, d52351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3887 q = 1) (hb : d55915 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3887, d55915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3887, d55915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55626 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3888 q = 1) (hb : d55916 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3888, d55916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3888, d55916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3889 q = 1) (hb : d55917 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3889, d55917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3889, d55917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6698 (p : Pattern) (ha : d3895 p = 1) (hb : d55923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3890 q = 1) (hb : d55918 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3890, d55918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3890, d55918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6697 q ha hb
  have h2 (q : Pattern) (ha : d3891 q = 1) (hb : d55919 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3891, d55919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3891, d55919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3892 q = 1) (hb : d55920 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3892, d55920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3892, d55920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3893 q = 1) (hb : d55921 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3893, d55921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3893, d55921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3894 q = 1) (hb : d55922 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3894, d55922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3894, d55922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3895 q = 1) (hb : d55923 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3895, d55923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3895, d55923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6699 (p : Pattern) (ha : d3908 p = 1) (hb : d55928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55925 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3903 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3903, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6567 q ha hb
    | true =>
      simp only [d3903, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6568 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3904 q = 1) (hb : d52571 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3904, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3904, d52571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3905 q = 1) (hb : d52572 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3905, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3905, d52572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3906 q = 1) (hb : d55926 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3906, d55926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3906, d55926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55640 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3907 q = 1) (hb : d55927 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3907, d55927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3907, d55927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3908 q = 1) (hb : d55928 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3908, d55928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3908, d55928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6700 (p : Pattern) (ha : d3914 p = 1) (hb : d55934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3909 q = 1) (hb : d55929 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3909, d55929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3909, d55929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6699 q ha hb
  have h2 (q : Pattern) (ha : d3910 q = 1) (hb : d55930 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3910, d55930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3910, d55930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3911 q = 1) (hb : d55931 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3911, d55931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3911, d55931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3912 q = 1) (hb : d55932 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3912, d55932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3912, d55932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3913 q = 1) (hb : d55933 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3913, d55933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3913, d55933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3914 q = 1) (hb : d55934 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3914, d55934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3914, d55934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6701 (p : Pattern) (ha : d3928 p = 1) (hb : d55940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55937 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3923 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3923, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6571 q ha hb
    | true =>
      simp only [d3923, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6572 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3924 q = 1) (hb : d52851 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3924, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3924, d52851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3925 q = 1) (hb : d52852 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3925, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3925, d52852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3926 q = 1) (hb : d55938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3926, d55938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3926, d55938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55655 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3927 q = 1) (hb : d55939 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3927, d55939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3927, d55939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3928 q = 1) (hb : d55940 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3928, d55940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3928, d55940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6702 (p : Pattern) (ha : d3934 p = 1) (hb : d55946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3929 q = 1) (hb : d55941 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3929, d55941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3929, d55941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6701 q ha hb
  have h2 (q : Pattern) (ha : d3930 q = 1) (hb : d55942 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3930, d55942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3930, d55942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3931 q = 1) (hb : d55943 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3931, d55943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3931, d55943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3932 q = 1) (hb : d55944 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3932, d55944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3932, d55944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3933 q = 1) (hb : d55945 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3933, d55945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3933, d55945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3934 q = 1) (hb : d55946 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3934, d55946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3934, d55946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6703 (p : Pattern) (ha : d3949 p = 1) (hb : d55953 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55950 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3944 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3944, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6575 q ha hb
    | true =>
      simp only [d3944, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6576 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3945 q = 1) (hb : d53166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3945, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3945, d53166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3946 q = 1) (hb : d53167 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3946, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3946, d53167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3947 q = 1) (hb : d55951 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3947, d55951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3947, d55951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55671 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3948 q = 1) (hb : d55952 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3948, d55952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3948, d55952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3949 q = 1) (hb : d55953 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3949, d55953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3949, d55953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6704 (p : Pattern) (ha : d3955 p = 1) (hb : d55959 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3950 q = 1) (hb : d55954 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3950, d55954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3950, d55954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6703 q ha hb
  have h2 (q : Pattern) (ha : d3951 q = 1) (hb : d55955 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3951, d55955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3951, d55955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3952 q = 1) (hb : d55956 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3952, d55956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3952, d55956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3953 q = 1) (hb : d55957 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3953, d55957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3953, d55957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3954 q = 1) (hb : d55958 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3954, d55958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3954, d55958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3955 q = 1) (hb : d55959 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3955, d55959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3955, d55959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6705 (p : Pattern) (ha : d3971 p = 1) (hb : d55967 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d55964 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3966 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3966, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6579 q ha hb
    | true =>
      simp only [d3966, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6580 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d3967 q = 1) (hb : d53483 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3967, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3967, d53483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d3968 q = 1) (hb : d53484 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3968, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3968, d53484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3969 q = 1) (hb : d55965 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3969, d55965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3969, d55965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d55688 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d3970 q = 1) (hb : d55966 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3970, d55966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3970, d55966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3971 q = 1) (hb : d55967 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3971, d55967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d3971, d55967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h9 p ha hb
theorem andIntro6706 (p : Pattern) (ha : d3977 p = 1) (hb : d55973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3972 q = 1) (hb : d55968 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3972, d55968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3972, d55968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6705 q ha hb
  have h2 (q : Pattern) (ha : d3973 q = 1) (hb : d55969 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3973, d55969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3973, d55969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3974 q = 1) (hb : d55970 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3974, d55970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3974, d55970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3975 q = 1) (hb : d55971 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3975, d55971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3975, d55971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3976 q = 1) (hb : d55972 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3976, d55972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3976, d55972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3977 q = 1) (hb : d55973 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3977, d55973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3977, d55973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6707 (p : Pattern) (ha : d3983 p = 1) (hb : d55979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d3896 q = 1) (hb : d55924 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3896, d55924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6696 q ha hb
    | true =>
      simp only [d3896, d55924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6698 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d3915 q = 1) (hb : d55935 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3915, d55935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3915, d55935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6700 q ha hb
  have h3 (q : Pattern) (ha : d3916 q = 1) (hb : d55936 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3916, d55936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3916, d55936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3935 q = 1) (hb : d55947 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3935, d55947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3935, d55947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6702 q ha hb
  have h5 (q : Pattern) (ha : d3936 q = 1) (hb : d55948 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3936, d55948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3936, d55948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3937 q = 1) (hb : d55949 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3937, d55949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3937, d55949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3956 q = 1) (hb : d55960 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3956, d55960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3956, d55960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6704 q ha hb
  have h8 (q : Pattern) (ha : d3957 q = 1) (hb : d55961 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3957, d55961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3957, d55961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3958 q = 1) (hb : d55962 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3958, d55962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3958, d55962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3959 q = 1) (hb : d55963 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3959, d55963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d3959, d55963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3978 q = 1) (hb : d55974 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3978, d55974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3978, d55974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6706 q ha hb
  have h12 (q : Pattern) (ha : d3979 q = 1) (hb : d55975 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3979, d55975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3979, d55975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3980 q = 1) (hb : d55976 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3980, d55976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3980, d55976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d3981 q = 1) (hb : d55977 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3981, d55977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3981, d55977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d3982 q = 1) (hb : d55978 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3982, d55978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3982, d55978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d3983 q = 1) (hb : d55979 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3983, d55979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d3983, d55979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro6708 (p : Pattern) (ha : d3989 p = 1) (hb : d55985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3984 q = 1) (hb : d55980 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3984, d55980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6707 q ha hb
    | true =>
      simp only [d3984, d55980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3985 q = 1) (hb : d55981 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3985, d55981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3985, d55981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3986 q = 1) (hb : d55982 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3986, d55982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3986, d55982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3987 q = 1) (hb : d55983 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3987, d55983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3987, d55983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3988 q = 1) (hb : d55984 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3988, d55984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3988, d55984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3989 q = 1) (hb : d55985 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3989, d55985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3989, d55985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6709 (p : Pattern) (ha : d3995 p = 1) (hb : d55991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3990 q = 1) (hb : d55986 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3990, d55986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6708 q ha hb
    | true =>
      simp only [d3990, d55986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3991 q = 1) (hb : d55987 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3991, d55987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3991, d55987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3992 q = 1) (hb : d55988 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3992, d55988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3992, d55988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3993 q = 1) (hb : d55989 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3993, d55989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3993, d55989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d3994 q = 1) (hb : d55990 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3994, d55990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3994, d55990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3995 q = 1) (hb : d55991 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3995, d55991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3995, d55991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6710 (p : Pattern) (ha : d4001 p = 1) (hb : d55997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3996 q = 1) (hb : d55992 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3996, d55992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6709 q ha hb
    | true =>
      simp only [d3996, d55992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d3997 q = 1) (hb : d55993 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3997, d55993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3997, d55993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3998 q = 1) (hb : d55994 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3998, d55994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3998, d55994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3999 q = 1) (hb : d55995 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3999, d55995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d3999, d55995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4000 q = 1) (hb : d55996 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d4000, d55996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4000, d55996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4001 q = 1) (hb : d55997 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d4001, d55997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4001, d55997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6711 (p : Pattern) (ha : d4007 p = 1) (hb : d56003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4002 q = 1) (hb : d55998 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d4002, d55998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6710 q ha hb
    | true =>
      simp only [d4002, d55998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4003 q = 1) (hb : d55999 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d4003, d55999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4003, d55999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4004 q = 1) (hb : d56000 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d4004, d56000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4004, d56000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4005 q = 1) (hb : d56001 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d4005, d56001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4005, d56001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4006 q = 1) (hb : d56002 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d4006, d56002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4006, d56002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4007 q = 1) (hb : d56003 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d4007, d56003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4007, d56003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6712 (p : Pattern) (ha : d4013 p = 1) (hb : d56009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4008 q = 1) (hb : d56004 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4008, d56004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6711 q ha hb
    | true =>
      simp only [d4008, d56004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4009 q = 1) (hb : d56005 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4009, d56005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4009, d56005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4010 q = 1) (hb : d56006 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4010, d56006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4010, d56006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4011 q = 1) (hb : d56007 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4011, d56007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4011, d56007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4012 q = 1) (hb : d56008 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4012, d56008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4012, d56008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4013 q = 1) (hb : d56009 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4013, d56009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4013, d56009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6713 (p : Pattern) (ha : d4019 p = 1) (hb : d56015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4014 q = 1) (hb : d56010 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4014, d56010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6712 q ha hb
    | true =>
      simp only [d4014, d56010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4015 q = 1) (hb : d56011 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4015, d56011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4015, d56011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4016 q = 1) (hb : d56012 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4016, d56012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4016, d56012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4017 q = 1) (hb : d56013 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4017, d56013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4017, d56013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4018 q = 1) (hb : d56014 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4018, d56014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4018, d56014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4019 q = 1) (hb : d56015 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4019, d56015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4019, d56015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6714 (p : Pattern) (ha : d4025 p = 1) (hb : d56021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4020 q = 1) (hb : d56016 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4020, d56016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6713 q ha hb
    | true =>
      simp only [d4020, d56016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4021 q = 1) (hb : d56017 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4021, d56017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4021, d56017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4022 q = 1) (hb : d56018 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4022, d56018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4022, d56018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4023 q = 1) (hb : d56019 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4023, d56019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4023, d56019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4024 q = 1) (hb : d56020 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4024, d56020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4024, d56020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4025 q = 1) (hb : d56021 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4025, d56021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4025, d56021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6715 (p : Pattern) (ha : d0 p = 1) (hb : d66091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d66091 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6716 (p : Pattern) (ha : d4013 p = 1) (hb : d74056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4008 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6650 q ha hb
    | true =>
      simp only [d4008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4009 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4010 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4011 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4012 q = 1) (hb : d74048 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4013 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d4013, d74056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4013, d74056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro6717 (p : Pattern) (ha : d4019 p = 1) (hb : d74056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4014 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6716 q ha hb
    | true =>
      simp only [d4014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4015 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4016 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4017 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4018 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4019 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6718 (p : Pattern) (ha : d4025 p = 1) (hb : d74056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4020 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6717 q ha hb
    | true =>
      simp only [d4020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d4021 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d4022 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4023 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4024 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4025 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6719 (p : Pattern) (ha : d0 p = 1) (hb : d74056 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74056 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro6720 (p : Pattern) (ha : d123 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d39 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d121 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d121, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d122 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d122, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6721 (p : Pattern) (ha : d3845 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d124 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6720 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d126 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3843 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3843, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3843, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3844 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3844, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3845 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6722 (p : Pattern) (ha : d199 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d39 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d121 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d121, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d122 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d122, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d199 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6723 (p : Pattern) (ha : d3848 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d124 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6720 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d126 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3843 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3843, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3843, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3844 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3844, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3844, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d200 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6722 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d201 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3846 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3846, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3846, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3847 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3847, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3847, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3848 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6724 (p : Pattern) (ha : d3854 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3849 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6721 q ha hb
    | true =>
      simp only [d3849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6723 q ha hb
  have h2 (q : Pattern) (ha : d3850 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3851 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3852 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3853 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3854 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6725 (p : Pattern) (ha : d303 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d153 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d301 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d301, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d302 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d302, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d303 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6726 (p : Pattern) (ha : d3862 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d304 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6725 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6720 q ha hb
  have h4 (q : Pattern) (ha : d305 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d306 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3860 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3860, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3860, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3861 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3861, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3862 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6727 (p : Pattern) (ha : d381 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d301 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d302 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d302, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d381 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6728 (p : Pattern) (ha : d3865 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d304 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6725 q ha hb
    | true =>
      simp only [d304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6720 q ha hb
  have h3 (q : Pattern) (ha : d305 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d306 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3860 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3860, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3860, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3861 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3861, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3861, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d382 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6727 q ha hb
    | true =>
      simp only [d382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6722 q ha hb
  have h9 (q : Pattern) (ha : d383 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d384 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3863 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3863, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3863, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3864 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3864, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3864, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3865 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6729 (p : Pattern) (ha : d3871 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3866 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6726 q ha hb
    | true =>
      simp only [d3866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6728 q ha hb
  have h2 (q : Pattern) (ha : d3867 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3868 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3869 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3870 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3871 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6730 (p : Pattern) (ha : d3877 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3855 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6724 q ha hb
  have h2 (q : Pattern) (ha : d3856 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3857 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3858 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3859 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3872 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6729 q ha hb
  have h7 (q : Pattern) (ha : d3873 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3874 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3875 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d3876 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d3877 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro6731 (p : Pattern) (ha : d521 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d484 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d519 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d519, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d520 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d520, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d521 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6732 (p : Pattern) (ha : d524 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d488 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d522 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d522, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d523, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6733 (p : Pattern) (ha : d3880 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d525 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6731 q ha hb
    | true =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6732 q ha hb
  have h4 (q : Pattern) (ha : d526 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d527 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3878 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3878, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3878, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3879 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3879, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3880 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6734 (p : Pattern) (ha : d615 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d484 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d519 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d519, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d520 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d520, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d615 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6735 (p : Pattern) (ha : d616 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d522 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d523 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d523, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6736 (p : Pattern) (ha : d3883 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d525 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6731 q ha hb
    | true =>
      simp only [d525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6732 q ha hb
  have h3 (q : Pattern) (ha : d526 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d527 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3878 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3878, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3878, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3879 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3879, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3879, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d617 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6734 q ha hb
    | true =>
      simp only [d617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6735 q ha hb
  have h9 (q : Pattern) (ha : d618 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d619 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3881 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3881, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3881, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3882 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3882, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3882, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3883 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6737 (p : Pattern) (ha : d3889 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3884 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6733 q ha hb
    | true =>
      simp only [d3884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6736 q ha hb
  have h2 (q : Pattern) (ha : d3885 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3886 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3887 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3888 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3889 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6738 (p : Pattern) (ha : d3895 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3890 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6737 q ha hb
  have h2 (q : Pattern) (ha : d3891 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3892 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3893 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3894 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3895 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6739 (p : Pattern) (ha : d813 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d776 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d811 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d811, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d812 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d812, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d813 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6740 (p : Pattern) (ha : d816 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d780 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d814 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d814, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d815, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6741 (p : Pattern) (ha : d3899 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d817 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6739 q ha hb
    | true =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6740 q ha hb
  have h4 (q : Pattern) (ha : d818 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d819 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3897 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3897, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3897, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3898 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3898, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3899 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro6742 (p : Pattern) (ha : d921 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d811 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d812 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d812, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d921 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6743 (p : Pattern) (ha : d922 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d780 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d814 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d815 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d815, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6744 (p : Pattern) (ha : d3902 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d817 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6739 q ha hb
    | true =>
      simp only [d817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6740 q ha hb
  have h3 (q : Pattern) (ha : d818 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d819 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d3897 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3897, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3897, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d3898 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3898, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3898, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d923 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6742 q ha hb
    | true =>
      simp only [d923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6743 q ha hb
  have h9 (q : Pattern) (ha : d924 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d925 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d3900 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3900, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d3900, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d3901 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3901, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3901, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d3902 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d3902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro6745 (p : Pattern) (ha : d3908 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3903 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6741 q ha hb
    | true =>
      simp only [d3903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6744 q ha hb
  have h2 (q : Pattern) (ha : d3904 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d3905 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d3905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d3906 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3907 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d3907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d3908 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro6746 (p : Pattern) (ha : d3914 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d3909 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6745 q ha hb
  have h2 (q : Pattern) (ha : d3910 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d3911 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d3912 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d3913 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d3914 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6747 (p : Pattern) (ha : d1192 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1190 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1190, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1191 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1191, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1192 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6748 (p : Pattern) (ha : d1195 p = 1) (hb : d74044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1193 q = 1) (hb : d66277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1193, d66277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1194, d74044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro6749 (p : Pattern) (ha : d3919 p = 1) (hb : d74062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d74060 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1196 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6747 q ha hb
    | true =>
      simp only [d1196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro6748 q ha hb
  have h4 (q : Pattern) (ha : d1197 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1198 q = 1) (hb : d74044 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d3917 q = 1) (hb : d74061 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d3917, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d3917, d74061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d3918 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d3918, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d3918, d74062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d3919 q = 1) (hb : d74062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d3919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
end NetHack.Soko22Hazard87
