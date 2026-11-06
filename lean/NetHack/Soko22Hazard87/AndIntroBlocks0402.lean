import NetHack.Soko22Hazard87.AndIntroBlocks0401
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro100500 (p : Pattern) (ha : d308 p = 1) (hb : d43111 p = 1) : d364655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42899 q = 1) : d364562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100494 q ha hb
    | true =>
      simp only [d42899, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100495 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42900 q = 1) : d364563 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42900, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42901 q = 1) : d364564 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42902 q = 1) : d364565 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42902, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42903 q = 1) : d364566 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42903, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43106 q = 1) : d364650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43106, d364650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100495 q ha hb
    | true =>
      simp only [d43106, d364650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43107 q = 1) : d364651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43107, d364651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43107, d364651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43108 q = 1) : d364652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43108, d364652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43108, d364652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43109 q = 1) : d364653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43109, d364653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43109, d364653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43110 q = 1) : d364654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43110, d364654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43110, d364654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43111 q = 1) : d364655 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43111, d364655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43111, d364655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100501 (p : Pattern) (ha : d308 p = 1) (hb : d43117 p = 1) : d364661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43106 q = 1) : d364650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43106, d364650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100495 q ha hb
    | true =>
      simp only [d43106, d364650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43107 q = 1) : d364651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43107, d364651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43107, d364651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43108 q = 1) : d364652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43108, d364652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43108, d364652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43109 q = 1) : d364653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43109, d364653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43109, d364653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43110 q = 1) : d364654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43110, d364654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43110, d364654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43112 q = 1) : d364656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43112, d364656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100498 q ha hb
    | true =>
      simp only [d43112, d364656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43113 q = 1) : d364657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43113, d364657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43113, d364657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43114 q = 1) : d364658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43114, d364658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43114, d364658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43115 q = 1) : d364659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43115, d364659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43115, d364659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43116 q = 1) : d364660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43116, d364660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43116, d364660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43117 q = 1) : d364661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43117, d364661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43117, d364661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100502 (p : Pattern) (ha : d308 p = 1) (hb : d43126 p = 1) : d364670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43112 q = 1) : d364656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43112, d364656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100498 q ha hb
    | true =>
      simp only [d43112, d364656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43113 q = 1) : d364657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43113, d364657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43113, d364657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43114 q = 1) : d364658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43114, d364658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43114, d364658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43115 q = 1) : d364659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43115, d364659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43115, d364659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43116 q = 1) : d364660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43116, d364660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43116, d364660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43126 q = 1) : d364670 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43126, d364670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43126, d364670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100503 (p : Pattern) (ha : d308 p = 1) (hb : d43163 p = 1) : d364703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42472 q = 1) : d364682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42472, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42472, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100489 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42370 q = 1) : d364517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100489 q ha hb
    | true =>
      simp only [d42370, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42473 q = 1) : d364683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42473, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42473, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42371 q = 1) : d364518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42371, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42474 q = 1) : d364684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42474, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42474, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42475 q = 1) : d364685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42475, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42475, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43147 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43147, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42865 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
    | true =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43148 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43148, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42866 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43149 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43149, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43150 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43150, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43162 q = 1) : d364702 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43162, d364702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43162, d364702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43156 q = 1) : d364696 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43156, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43163 q = 1) : d364703 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43163, d364703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43163, d364703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100504 (p : Pattern) (ha : d308 p = 1) (hb : d43167 p = 1) : d364707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43147 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43147, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42865 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
    | true =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43148 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43148, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42866 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43149 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43149, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43150 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43150, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43156 q = 1) : d364696 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43156, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43167 q = 1) : d364707 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43167, d364707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43167, d364707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100505 (p : Pattern) (ha : d308 p = 1) (hb : d43186 p = 1) : d364726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43168 q = 1) : d364708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100503 q ha hb
    | true =>
      simp only [d43168, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100504 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43169 q = 1) : d364709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43169, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43170 q = 1) : d364710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43170, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43176 q = 1) : d364716 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43176, d364716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43176, d364716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43185 q = 1) : d364725 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43185, d364725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43185, d364725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43186 q = 1) : d364726 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43186, d364726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43186, d364726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100506 (p : Pattern) (ha : d308 p = 1) (hb : d43257 p = 1) : d364749 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43187 q = 1) : d364727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43187, d364727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100505 q ha hb
    | true =>
      simp only [d43187, d364727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43188 q = 1) : d364728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43188, d364728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43188, d364728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43254 q = 1) : d364746 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43254, d364746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43254, d364746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43255 q = 1) : d364747 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43255, d364747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43255, d364747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43256 q = 1) : d364748 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43256, d364748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43256, d364748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43257 q = 1) : d364749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43257, d364749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43257, d364749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100507 (p : Pattern) (ha : d308 p = 1) (hb : d43263 p = 1) : d364755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43258 q = 1) : d364750 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43258, d364750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100506 q ha hb
    | true =>
      simp only [d43258, d364750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43259 q = 1) : d364751 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43259, d364751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43259, d364751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43260 q = 1) : d364752 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43260, d364752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43260, d364752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43261 q = 1) : d364753 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43261, d364753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43261, d364753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43262 q = 1) : d364754 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43262, d364754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43262, d364754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43263 q = 1) : d364755 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43263, d364755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43263, d364755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100508 (p : Pattern) (ha : d308 p = 1) (hb : d42919 p = 1) : d364582 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42891 q = 1) : d364554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42892 q = 1) : d364555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42918 q = 1) : d364581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42918, d364581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42918, d364581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42919 q = 1) : d364582 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42919, d364582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42919, d364582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100509 (p : Pattern) (ha : d308 p = 1) (hb : d42921 p = 1) : d364584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42895 q = 1) : d364558 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42896 q = 1) : d364559 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42920 q = 1) : d364583 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42920, d364583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42920, d364583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42921 q = 1) : d364584 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42921, d364584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42921, d364584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100510 (p : Pattern) (ha : d308 p = 1) (hb : d42928 p = 1) : d364591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42891 q = 1) : d364554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42926 q = 1) : d364589 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42926, d364589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42926, d364589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42927 q = 1) : d364590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42927, d364590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42927, d364590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42928 q = 1) : d364591 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42928, d364591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42928, d364591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100511 (p : Pattern) (ha : d308 p = 1) (hb : d42931 p = 1) : d364594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42895 q = 1) : d364558 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42929 q = 1) : d364592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42929, d364592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42929, d364592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42930 q = 1) : d364593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42930, d364593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42930, d364593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42931 q = 1) : d364594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42931, d364594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42931, d364594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100512 (p : Pattern) (ha : d308 p = 1) (hb : d42954 p = 1) : d363918 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d42938 q = 1) : d42938 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42595 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d42595, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42596 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42596, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42939 q = 1) : d363912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42939, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42939, d363912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42942 q = 1) : d43868 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100303 q ha hb
    | true =>
      simp only [d42942, d43868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42943 q = 1) : d43869 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42943, d43869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42946 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100304 q ha hb
    | true =>
      simp only [d42946, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42947 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42947, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42948 q = 1) : d43870 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42948, d43870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42948, d43870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42949 q = 1) : d363913 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42949, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42949, d363913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42950 q = 1) : d363914 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42950, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42950, d363914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42364 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42365 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42597 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42597, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42951 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42951, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42951, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42952 q = 1) : d363916 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42952, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42952, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42953 q = 1) : d363917 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42953, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42953, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d42954 q = 1) : d363918 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42954, d363918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42954, d363918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro100513 (p : Pattern) (ha : d308 p = 1) (hb : d42967 p = 1) : d363925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42595 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d42595, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42596 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42364 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100301 q ha hb
    | true =>
      simp only [d42364, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42365 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42365, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42597 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42597, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42602 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100306 q ha hb
    | true =>
      simp only [d42602, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42603 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42604 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42605 q = 1) : d363916 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42605, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42605, d363916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42606 q = 1) : d363917 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42606, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42606, d363917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42962 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100307 q ha hb
    | true =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42963 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42964 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42964, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42964, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42965 q = 1) : d363923 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42965, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42965, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42966 q = 1) : d363924 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42966, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42966, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42967 q = 1) : d363925 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42967, d363925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42967, d363925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100514 (p : Pattern) (ha : d308 p = 1) (hb : d42976 p = 1) : d363933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42595 q = 1) : d363910 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100302 q ha hb
    | true =>
      simp only [d42595, d363910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42596 q = 1) : d363911 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d363911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42962 q = 1) : d43857 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100307 q ha hb
    | true =>
      simp only [d42962, d43857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42963 q = 1) : d43858 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42963, d43858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42973 q = 1) : d363915 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42973, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42973, d363915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42974 q = 1) : d363931 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42974, d363931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42974, d363931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42975 q = 1) : d363932 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42975, d363932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42975, d363932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42964 q = 1) : d43912 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42964, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42964, d43912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42965 q = 1) : d363923 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42965, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42965, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42966 q = 1) : d363924 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42966, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42966, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42976 q = 1) : d363933 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42976, d363933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42976, d363933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro100515 (p : Pattern) (ha : d308 p = 1) (hb : d42982 p = 1) : d364599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42955 q = 1) : d363919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42955, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100512 q ha hb
    | true =>
      simp only [d42955, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42956 q = 1) : d363920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42956, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42956, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42957 q = 1) : d363921 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42957, d363921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42957, d363921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42958 q = 1) : d363922 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42958, d363922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42958, d363922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42968 q = 1) : d363926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42968, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100513 q ha hb
    | true =>
      simp only [d42968, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42969 q = 1) : d363927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42969, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42969, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42970 q = 1) : d363928 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42970, d363928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42970, d363928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42971 q = 1) : d363929 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42971, d363929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42971, d363929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42972 q = 1) : d363930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42972, d363930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42972, d363930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42977 q = 1) : d363934 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42977, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100514 q ha hb
    | true =>
      simp only [d42977, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42978 q = 1) : d363935 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42978, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42978, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42979 q = 1) : d363936 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42979, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42979, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42980 q = 1) : d363937 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42980, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42980, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42621 q = 1) : d364523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
    | true =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42622 q = 1) : d364524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42623 q = 1) : d364525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42623, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42624 q = 1) : d364526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42624, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42981 q = 1) : d364598 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42981, d364598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42981, d364598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42982 q = 1) : d364599 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42982, d364599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42982, d364599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100516 (p : Pattern) (ha : d308 p = 1) (hb : d42986 p = 1) : d364603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42621 q = 1) : d364523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
    | true =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42622 q = 1) : d364524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42623 q = 1) : d364525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42623, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42624 q = 1) : d364526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42624, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42865 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
    | true =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42866 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42867 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42867, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42868 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42868, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42869 q = 1) : d364532 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42869, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42869, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42872 q = 1) : d364535 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42872, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42986 q = 1) : d364603 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42986, d364603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42986, d364603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100517 (p : Pattern) (ha : d308 p = 1) (hb : d42992 p = 1) : d364609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42983 q = 1) : d364600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42983, d364600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100515 q ha hb
    | true =>
      simp only [d42983, d364600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100488 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42984 q = 1) : d364601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42984, d364601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42984, d364601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42985 q = 1) : d364602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42985, d364602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42985, d364602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42987 q = 1) : d364604 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42987, d364604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100488 q ha hb
    | true =>
      simp only [d42987, d364604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100516 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42988 q = 1) : d364605 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42988, d364605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42988, d364605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42989 q = 1) : d364606 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42989, d364606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42989, d364606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42990 q = 1) : d364607 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42990, d364607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42990, d364607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42874 q = 1) : d364537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42874, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100488 q ha hb
    | true =>
      simp only [d42874, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100490 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42875 q = 1) : d364538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42875, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42875, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42876 q = 1) : d364539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42876, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42876, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42878 q = 1) : d364541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100490 q ha hb
    | true =>
      simp only [d42878, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100491 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42879 q = 1) : d364542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42879, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42880 q = 1) : d364543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42880, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42881 q = 1) : d364544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42881, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42881, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42991 q = 1) : d364608 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42991, d364608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42991, d364608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42992 q = 1) : d364609 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42992, d364609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42992, d364609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100518 (p : Pattern) (ha : d308 p = 1) (hb : d42998 p = 1) : d364615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42993 q = 1) : d364610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42993, d364610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100517 q ha hb
    | true =>
      simp only [d42993, d364610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42994 q = 1) : d364611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42994, d364611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42994, d364611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42995 q = 1) : d364612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42995, d364612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42995, d364612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42996 q = 1) : d364613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42996, d364613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42996, d364613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42997 q = 1) : d364614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42997, d364614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42997, d364614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42998 q = 1) : d364615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42998, d364615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42998, d364615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100519 (p : Pattern) (ha : d308 p = 1) (hb : d43074 p = 1) : d364621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43071 q = 1) : d364618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43071, d364618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43071, d364618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43072 q = 1) : d364619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43072, d364619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43072, d364619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43073 q = 1) : d364620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43073, d364620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43073, d364620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43074 q = 1) : d364621 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43074, d364621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43074, d364621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100520 (p : Pattern) (ha : d308 p = 1) (hb : d309888 p = 1) : d364627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42922 q = 1) : d364585 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42922, d364585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100508 q ha hb
    | true =>
      simp only [d42922, d364585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100509 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42923 q = 1) : d364586 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42923, d364586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42923, d364586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42924 q = 1) : d364587 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42924, d364587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42924, d364587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42925 q = 1) : d364588 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42925, d364588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42925, d364588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42932 q = 1) : d364595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42932, d364595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100510 q ha hb
    | true =>
      simp only [d42932, d364595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100511 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42933 q = 1) : d364596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42933, d364596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42933, d364596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42934 q = 1) : d364597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42934, d364597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42934, d364597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42999 q = 1) : d364616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42999, d364616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100518 q ha hb
    | true =>
      simp only [d42999, d364616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100494 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309884 q = 1) : d364617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d364617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309884, d364617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43075 q = 1) : d364622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43075, d364622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100519 q ha hb
    | true =>
      simp only [d43075, d364622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43076 q = 1) : d364623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43076, d364623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43076, d364623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309885 q = 1) : d364624 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d364624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309885, d364624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309886 q = 1) : d364625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d364625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309886, d364625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309887 q = 1) : d364626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d364626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309887, d364626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309888 q = 1) : d364627 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309888, d364627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309888, d364627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100521 (p : Pattern) (ha : d308 p = 1) (hb : d43081 p = 1) : d364628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42891 q = 1) : d364554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42892 q = 1) : d364555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42918 q = 1) : d364581 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42918, d364581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42918, d364581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43081 q = 1) : d364628 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43081, d364628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43081, d364628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100522 (p : Pattern) (ha : d308 p = 1) (hb : d43082 p = 1) : d364629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42895 q = 1) : d364558 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42896 q = 1) : d364559 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42920 q = 1) : d364583 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42920, d364583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42920, d364583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43082 q = 1) : d364629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43082, d364629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43082, d364629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100523 (p : Pattern) (ha : d308 p = 1) (hb : d43087 p = 1) : d364634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42891 q = 1) : d364554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42926 q = 1) : d364589 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42926, d364589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42926, d364589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42927 q = 1) : d364590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42927, d364590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42927, d364590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43087 q = 1) : d364634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43087, d364634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43087, d364634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100524 (p : Pattern) (ha : d308 p = 1) (hb : d43088 p = 1) : d364635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42889 q = 1) : d364552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100493 q ha hb
    | true =>
      simp only [d42889, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42890 q = 1) : d364553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42890, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42895 q = 1) : d364558 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42929 q = 1) : d364592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42929, d364592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42929, d364592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42930 q = 1) : d364593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42930, d364593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42930, d364593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43088 q = 1) : d364635 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43088, d364635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43088, d364635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100525 (p : Pattern) (ha : d308 p = 1) (hb : d43092 p = 1) : d364639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42993 q = 1) : d364610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42993, d364610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100517 q ha hb
    | true =>
      simp only [d42993, d364610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42994 q = 1) : d364611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42994, d364611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42994, d364611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42995 q = 1) : d364612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42995, d364612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42995, d364612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42996 q = 1) : d364613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42996, d364613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42996, d364613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42997 q = 1) : d364614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42997, d364614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42997, d364614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43092 q = 1) : d364639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43092, d364639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43092, d364639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100526 (p : Pattern) (ha : d308 p = 1) (hb : d43098 p = 1) : d364642 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42885 q = 1) : d364548 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100492 q ha hb
    | true =>
      simp only [d42885, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42886 q = 1) : d364549 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42886, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43071 q = 1) : d364618 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43071, d364618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43071, d364618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43072 q = 1) : d364619 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43072, d364619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43072, d364619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43073 q = 1) : d364620 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43073, d364620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43073, d364620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43098 q = 1) : d364642 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43098, d364642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43098, d364642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100527 (p : Pattern) (ha : d308 p = 1) (hb : d309893 p = 1) : d364648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42922 q = 1) : d364585 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42922, d364585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100508 q ha hb
    | true =>
      simp only [d42922, d364585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100509 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42923 q = 1) : d364586 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42923, d364586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42923, d364586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42924 q = 1) : d364587 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42924, d364587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42924, d364587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42925 q = 1) : d364588 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42925, d364588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42925, d364588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42932 q = 1) : d364595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42932, d364595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100510 q ha hb
    | true =>
      simp only [d42932, d364595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100511 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42933 q = 1) : d364596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42933, d364596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42933, d364596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42934 q = 1) : d364597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42934, d364597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42934, d364597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42999 q = 1) : d364616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42999, d364616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100518 q ha hb
    | true =>
      simp only [d42999, d364616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100494 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309884 q = 1) : d364617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d364617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309884, d364617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43075 q = 1) : d364622 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43075, d364622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100519 q ha hb
    | true =>
      simp only [d43075, d364622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43076 q = 1) : d364623 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43076, d364623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43076, d364623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309885 q = 1) : d364624 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d364624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309885, d364624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309886 q = 1) : d364625 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d364625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309886, d364625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309887 q = 1) : d364626 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d364626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309887, d364626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43083 q = 1) : d364630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43083, d364630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100521 q ha hb
    | true =>
      simp only [d43083, d364630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100522 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43084 q = 1) : d364631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43084, d364631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43084, d364631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d43085 q = 1) : d364632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43085, d364632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43085, d364632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43086 q = 1) : d364633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43086, d364633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43086, d364633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43089 q = 1) : d364636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43089, d364636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100523 q ha hb
    | true =>
      simp only [d43089, d364636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100524 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d43090 q = 1) : d364637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43090, d364637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43090, d364637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d43091 q = 1) : d364638 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43091, d364638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43091, d364638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d43093 q = 1) : d364640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43093, d364640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100525 q ha hb
    | true =>
      simp only [d43093, d364640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100497 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309889 q = 1) : d364641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d364641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309889, d364641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d43099 q = 1) : d364643 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43099, d364643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100526 q ha hb
    | true =>
      simp only [d43099, d364643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d43100 q = 1) : d364644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43100, d364644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43100, d364644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d309890 q = 1) : d364645 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d364645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309890, d364645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d309891 q = 1) : d364646 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309891, d364646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309891, d364646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d308 q = 1) (hb : d309892 q = 1) : d364647 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309892, d364647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309892, d364647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d308 q = 1) (hb : d309893 q = 1) : d364648 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309893, d364648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309893, d364648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro100528 (p : Pattern) (ha : d308 p = 1) (hb : d309900 p = 1) : d364668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43093 q = 1) : d364640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43093, d364640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100525 q ha hb
    | true =>
      simp only [d43093, d364640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100497 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309889 q = 1) : d364641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d364641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309889, d364641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43099 q = 1) : d364643 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43099, d364643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100526 q ha hb
    | true =>
      simp only [d43099, d364643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43100 q = 1) : d364644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43100, d364644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43100, d364644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309890 q = 1) : d364645 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d364645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309890, d364645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309898 q = 1) : d364666 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309898, d364666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309898, d364666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309899 q = 1) : d364667 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309899, d364667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309899, d364667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309900 q = 1) : d364668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309900, d364668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309900, d364668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100529 (p : Pattern) (ha : d308 p = 1) (hb : d43146 p = 1) : d364681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43132 q = 1) : d364136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43132, d364136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43132, d364136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100512 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42955 q = 1) : d363919 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42955, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100512 q ha hb
    | true =>
      simp only [d42955, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43133 q = 1) : d364137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43133, d364137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43133, d364137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42956 q = 1) : d363920 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42956, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42956, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43134 q = 1) : d364138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43134, d364138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43134, d364138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43135 q = 1) : d364139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43135, d364139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43135, d364139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43136 q = 1) : d364140 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43136, d364140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43136, d364140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100513 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42968 q = 1) : d363926 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42968, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100513 q ha hb
    | true =>
      simp only [d42968, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43137 q = 1) : d364141 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43137, d364141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43137, d364141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42969 q = 1) : d363927 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42969, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42969, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43138 q = 1) : d364142 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43138, d364142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43138, d364142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43139 q = 1) : d364143 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43139, d364143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43139, d364143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43140 q = 1) : d364144 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43140, d364144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43140, d364144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43141 q = 1) : d364130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43141, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43141, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100514 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42977 q = 1) : d363934 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42977, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100514 q ha hb
    | true =>
      simp only [d42977, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43142 q = 1) : d364131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43142, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43142, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42978 q = 1) : d363935 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42978, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42978, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43143 q = 1) : d364132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43143, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43143, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d43144 q = 1) : d364133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43144, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43144, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d42760 q = 1) : d364676 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42760, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d42621 q = 1) : d364523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
    | true =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d42761 q = 1) : d364677 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42761, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d42622 q = 1) : d364524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d42762 q = 1) : d364678 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d42762, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d42763 q = 1) : d364679 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42763, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d43145 q = 1) : d364680 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43145, d364680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43145, d364680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d43146 q = 1) : d364681 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43146, d364681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43146, d364681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100530 (p : Pattern) (ha : d308 p = 1) (hb : d43152 p = 1) : d364692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42751 q = 1) : d364160 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42751, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42751, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100484 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42608 q = 1) : d363948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100484 q ha hb
    | true =>
      simp only [d42608, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42752 q = 1) : d364161 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42752, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42752, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42609 q = 1) : d363949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42609, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42753 q = 1) : d364162 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42753, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42753, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42754 q = 1) : d364163 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42754, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42754, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42755 q = 1) : d364682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42755, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42755, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100485 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42613 q = 1) : d364517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100485 q ha hb
    | true =>
      simp only [d42613, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42756 q = 1) : d364683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42756, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42756, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42614 q = 1) : d364518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42614, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42757 q = 1) : d364684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42757, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42757, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42758 q = 1) : d364685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42758, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42758, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42759 q = 1) : d364686 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42759, d364686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42759, d364686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42760 q = 1) : d364676 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42760, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42621 q = 1) : d364523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
    | true =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42761 q = 1) : d364677 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42761, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42622 q = 1) : d364524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42762 q = 1) : d364678 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42762, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42763 q = 1) : d364679 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42763, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d43147 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43147, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d42865 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
    | true =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d43148 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43148, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d42866 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d43149 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d43149, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d43150 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43150, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d43151 q = 1) : d364691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43151, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43151, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d43152 q = 1) : d364692 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43152, d364692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43152, d364692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100531 (p : Pattern) (ha : d308 p = 1) (hb : d43157 p = 1) : d364697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42760 q = 1) : d364676 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42760, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42621 q = 1) : d364523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
    | true =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42761 q = 1) : d364677 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42761, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42622 q = 1) : d364524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42762 q = 1) : d364678 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42762, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42763 q = 1) : d364679 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42763, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43147 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43147, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42865 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100487 q ha hb
    | true =>
      simp only [d42865, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43148 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43148, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42866 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42866, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43149 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43149, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43150 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43150, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43151 q = 1) : d364691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43151, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43151, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43156 q = 1) : d364696 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43156, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43157 q = 1) : d364697 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43157, d364697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43157, d364697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100532 (p : Pattern) (ha : d308 p = 1) (hb : d43173 p = 1) : d364713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43153 q = 1) : d364693 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43153, d364693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100529 q ha hb
    | true =>
      simp only [d43153, d364693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100530 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43154 q = 1) : d364694 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43154, d364694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43154, d364694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43155 q = 1) : d364695 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43155, d364695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43155, d364695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43158 q = 1) : d364698 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43158, d364698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100530 q ha hb
    | true =>
      simp only [d43158, d364698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100531 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43159 q = 1) : d364699 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43159, d364699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43159, d364699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43160 q = 1) : d364700 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43160, d364700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43160, d364700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43161 q = 1) : d364701 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43161, d364701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43161, d364701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43164 q = 1) : d364704 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43164, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100530 q ha hb
    | true =>
      simp only [d43164, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100503 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43165 q = 1) : d364705 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43165, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43165, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43166 q = 1) : d364706 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43166, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43166, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d43168 q = 1) : d364708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100503 q ha hb
    | true =>
      simp only [d43168, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100504 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43169 q = 1) : d364709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43169, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d43170 q = 1) : d364710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43170, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d43171 q = 1) : d364711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43171, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43171, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d43172 q = 1) : d364712 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43172, d364712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43172, d364712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d43173 q = 1) : d364713 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43173, d364713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43173, d364713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100533 (p : Pattern) (ha : d308 p = 1) (hb : d43178 p = 1) : d364718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43164 q = 1) : d364704 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43164, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100530 q ha hb
    | true =>
      simp only [d43164, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100503 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43165 q = 1) : d364705 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43165, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43165, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43166 q = 1) : d364706 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43166, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43166, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43168 q = 1) : d364708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100503 q ha hb
    | true =>
      simp only [d43168, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100504 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43169 q = 1) : d364709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43169, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43170 q = 1) : d364710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43170, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43171 q = 1) : d364711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43171, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43171, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43176 q = 1) : d364716 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43176, d364716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43176, d364716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d43177 q = 1) : d364717 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43177, d364717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43177, d364717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d43178 q = 1) : d364718 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43178, d364718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43178, d364718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100534 (p : Pattern) (ha : d308 p = 1) (hb : d43184 p = 1) : d364724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43174 q = 1) : d364714 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43174, d364714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100532 q ha hb
    | true =>
      simp only [d43174, d364714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43175 q = 1) : d364715 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43175, d364715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43175, d364715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43179 q = 1) : d364719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100533 q ha hb
    | true =>
      simp only [d43179, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43180 q = 1) : d364720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43180, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43181 q = 1) : d364721 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43181, d364721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43181, d364721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43182 q = 1) : d364722 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43182, d364722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43182, d364722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43183 q = 1) : d364723 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43183, d364723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43183, d364723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43184 q = 1) : d364724 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43184, d364724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43184, d364724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100535 (p : Pattern) (ha : d308 p = 1) (hb : d43192 p = 1) : d364732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43179 q = 1) : d364719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100533 q ha hb
    | true =>
      simp only [d43179, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43180 q = 1) : d364720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43180, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43187 q = 1) : d364727 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43187, d364727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100505 q ha hb
    | true =>
      simp only [d43187, d364727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43188 q = 1) : d364728 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43188, d364728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43188, d364728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43189 q = 1) : d364729 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43189, d364729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43189, d364729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43190 q = 1) : d364730 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43190, d364730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43190, d364730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43191 q = 1) : d364731 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43191, d364731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43191, d364731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d43192 q = 1) : d364732 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43192, d364732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43192, d364732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100536 (p : Pattern) (ha : d308 p = 1) (hb : d43246 p = 1) : d364738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43179 q = 1) : d364719 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100533 q ha hb
    | true =>
      simp only [d43179, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d43180 q = 1) : d364720 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43180, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43243 q = 1) : d364735 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43243, d364735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43243, d364735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43244 q = 1) : d364736 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43244, d364736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43244, d364736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d43245 q = 1) : d364737 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43245, d364737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43245, d364737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d43246 q = 1) : d364738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43246, d364738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43246, d364738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100537 (p : Pattern) (ha : d308 p = 1) (hb : d309910 p = 1) : d364744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d43193 q = 1) : d364733 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43193, d364733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100534 q ha hb
    | true =>
      simp only [d43193, d364733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100535 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309906 q = 1) : d364734 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309906, d364734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309906, d364734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d43247 q = 1) : d364739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43247, d364739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100536 q ha hb
    | true =>
      simp only [d43247, d364739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d43248 q = 1) : d364740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43248, d364740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43248, d364740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309907 q = 1) : d364741 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309907, d364741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309907, d364741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309908 q = 1) : d364742 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309908, d364742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309908, d364742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309909 q = 1) : d364743 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309909, d364743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309909, d364743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309910 q = 1) : d364744 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309910, d364744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309910, d364744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100538 (p : Pattern) (ha : d308 p = 1) (hb : d309916 p = 1) : d364761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42905 q = 1) : d364568 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42905, d364568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42905, d364568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100496 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42906 q = 1) : d364569 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42906, d364569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42906, d364569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42915 q = 1) : d364578 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42915, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100496 q ha hb
    | true =>
      simp only [d42915, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100499 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42916 q = 1) : d364579 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42916, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42916, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42917 q = 1) : d364580 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42917, d364580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42917, d364580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309894 q = 1) : d364649 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309894, d364649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100520 q ha hb
    | true =>
      simp only [d309894, d364649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100527 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d43118 q = 1) : d364662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43118, d364662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100500 q ha hb
    | true =>
      simp only [d43118, d364662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100501 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309895 q = 1) : d364663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309895, d364663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309895, d364663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309896 q = 1) : d364664 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309896, d364664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309896, d364664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d309897 q = 1) : d364665 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309897, d364665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309897, d364665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d309901 q = 1) : d364669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309901, d364669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309901, d364669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100528 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d43127 q = 1) : d364671 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43127, d364671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43127, d364671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100502 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309902 q = 1) : d364672 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309902, d364672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309902, d364672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309903 q = 1) : d364673 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309903, d364673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309903, d364673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309904 q = 1) : d364674 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309904, d364674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309904, d364674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d309905 q = 1) : d364675 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309905, d364675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309905, d364675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d309911 q = 1) : d364745 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309911, d364745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309911, d364745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100537 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d43264 q = 1) : d364756 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43264, d364756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d43264, d364756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100507 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d309912 q = 1) : d364757 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309912, d364757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309912, d364757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d309913 q = 1) : d364758 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309913, d364758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309913, d364758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d309914 q = 1) : d364759 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309914, d364759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309914, d364759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d309915 q = 1) : d364760 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309915, d364760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309915, d364760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309916 q = 1) : d364761 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309916, d364761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309916, d364761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100539 (p : Pattern) (ha : d308 p = 1) (hb : d309922 p = 1) : d364767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d309917 q = 1) : d364762 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309917, d364762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309917, d364762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100538 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309918 q = 1) : d364763 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309918, d364763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309918, d364763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d309919 q = 1) : d364764 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309919, d364764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309919, d364764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d309920 q = 1) : d364765 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309920, d364765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309920, d364765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309921 q = 1) : d364766 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309921, d364766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309921, d364766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309922 q = 1) : d364767 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309922, d364767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309922, d364767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100540 (p : Pattern) (ha : d310011 p = 1) (hb : d364416 p = 1) : d364773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309923 q = 1) : d364768 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309923, d364768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309923, d364768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100539 q ha hb
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d364413 q = 1) : d364769 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d364413, d364769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309924, d364413, d364769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309966 q = 1) (hb : d364414 q = 1) : d364770 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d364414, d364770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d364414, d364770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310009 q = 1) (hb : d364415 q = 1) : d364771 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d364415, d364771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310009, d364415, d364771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310010 q = 1) (hb : d364416 q = 1) : d364772 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d364416, d364772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310010, d364416, d364772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d364416 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d310011 q = 1) (hb : d364416 q = 1) : d364773 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d364773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d310011, d364773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100541 (p : Pattern) (ha : d310017 p = 1) (hb : d364416 p = 1) : d364779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d364416 q = 1) : d364774 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d364774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100540 q ha hb
    | true =>
      simp only [d310012, d364774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d364416 q = 1) : d364775 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d364775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d364775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d364416 q = 1) : d364776 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d364776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d364776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d364416 q = 1) : d364777 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d364777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d364777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d364416 q = 1) : d364778 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d364778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d364778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310017 q = 1) (hb : d364416 q = 1) : d364779 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d364779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d364779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100542 (p : Pattern) (ha : d310023 p = 1) (hb : d364421 p = 1) : d364785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d364417 q = 1) : d364780 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d364417, d364780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100541 q ha hb
    | true =>
      simp only [d310018, d364417, d364780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d364418 q = 1) : d364781 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d364418, d364781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d364418, d364781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d364419 q = 1) : d364782 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d364419, d364782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d364419, d364782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d364420 q = 1) : d364783 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d364420, d364783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d364420, d364783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d364421 q = 1) : d364784 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d364421, d364784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d364421, d364784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310023 q = 1) (hb : d364421 q = 1) : d364785 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d364785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, d364785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100543 (p : Pattern) (ha : d310029 p = 1) (hb : d364421 p = 1) : d364791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d364421 q = 1) : d364786 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d364786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100542 q ha hb
    | true =>
      simp only [d310024, d364786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d364421 q = 1) : d364787 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d364787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d364787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d364421 q = 1) : d364788 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d364788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d364788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d364421 q = 1) : d364789 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d364789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d364789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d364421 q = 1) : d364790 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d364790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d364790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d364421 q = 1) : d364791 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d364791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d364791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100544 (p : Pattern) (ha : d310035 p = 1) (hb : d364421 p = 1) : d364797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d364421 q = 1) : d364792 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d364792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100543 q ha hb
    | true =>
      simp only [d310030, d364792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d364421 q = 1) : d364793 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d364793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d364793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d364421 q = 1) : d364794 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d364794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d364794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d364421 q = 1) : d364795 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d364795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d364795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d364421 q = 1) : d364796 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d364796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d364796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d364421 q = 1) : d364797 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d364797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d364797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100545 (p : Pattern) (ha : d310041 p = 1) (hb : d364421 p = 1) : d364803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d364421 q = 1) : d364798 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d364798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100544 q ha hb
    | true =>
      simp only [d310036, d364798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d364421 q = 1) : d364799 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d364799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d364799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d364421 q = 1) : d364800 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d364800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d364800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d364421 q = 1) : d364801 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d364801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d364801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d364421 q = 1) : d364802 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d364802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d364802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d364421 q = 1) : d364803 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d364803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d364803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100546 (p : Pattern) (ha : d310047 p = 1) (hb : d364421 p = 1) : d364809 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d364421 q = 1) : d364804 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d364804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100545 q ha hb
    | true =>
      simp only [d310042, d364804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d364421 q = 1) : d364805 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d364805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d364805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d364421 q = 1) : d364806 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d364806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d364806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d364421 q = 1) : d364807 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d364807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d364807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d364421 q = 1) : d364808 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d364808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d364808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d364421 q = 1) : d364809 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d364809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d364809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100547 (p : Pattern) (ha : d310053 p = 1) (hb : d364421 p = 1) : d364815 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d364421 q = 1) : d364810 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d364810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100546 q ha hb
    | true =>
      simp only [d310048, d364810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d364421 q = 1) : d364811 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d364811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d364811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d364421 q = 1) : d364812 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d364812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d364812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d364421 q = 1) : d364813 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d364813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d364813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d364421 q = 1) : d364814 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d364814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d364814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d364421 q = 1) : d364815 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d364815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d364815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100548 (p : Pattern) (ha : d361199 p = 1) (hb : d364527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1578 q = 1) (hb : d361196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d361197 q = 1) (hb : d364514 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361197, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d361197, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361198 q = 1) (hb : d364515 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361198, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361198, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361199 q = 1) (hb : d364527 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361199, d364527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361199, d364527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100549 (p : Pattern) (ha : d361205 p = 1) (hb : d364540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361200 q = 1) (hb : d364528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
    | true =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361201 q = 1) (hb : d364529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361202 q = 1) (hb : d364530 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361202, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361202, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361203 q = 1) (hb : d364531 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361203, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361203, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361204 q = 1) (hb : d364535 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361204, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361204, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361205 q = 1) (hb : d364540 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361205, d364540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361205, d364540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100550 (p : Pattern) (ha : d361310 p = 1) (hb : d364516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1578 q = 1) (hb : d361196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d361308 q = 1) (hb : d363938 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361308, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d361308, d363938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d361309 q = 1) (hb : d363939 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361309, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361309, d363939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361197 q = 1) (hb : d364514 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361197, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d361197, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d361198 q = 1) (hb : d364515 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361198, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361198, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361310 q = 1) (hb : d364516 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361310, d364516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361310, d364516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100551 (p : Pattern) (ha : d361316 p = 1) (hb : d364536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361311 q = 1) (hb : d364517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361311, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100550 q ha hb
    | true =>
      simp only [d361311, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361312 q = 1) (hb : d364518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361312, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361312, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361313 q = 1) (hb : d364519 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361313, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361313, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361314 q = 1) (hb : d364520 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361314, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361314, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361200 q = 1) (hb : d364528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
    | true =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361201 q = 1) (hb : d364529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361202 q = 1) (hb : d364530 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361202, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361202, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361203 q = 1) (hb : d364531 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361203, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361203, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361315 q = 1) (hb : d364534 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361315, d364534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361315, d364534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361204 q = 1) (hb : d364535 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361204, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361204, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361316 q = 1) (hb : d364536 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361316, d364536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361316, d364536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100552 (p : Pattern) (ha : d361443 p = 1) (hb : d364522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43857 q = 1) (hb : d361305 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100183 q ha hb
    | true =>
      simp only [d43857, d361305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43858 q = 1) (hb : d361306 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43858, d361306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1564 q = 1) (hb : d361194 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100001 q ha hb
    | true =>
      simp only [d1564, d361194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1565 q = 1) (hb : d361195 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1565, d361195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43912 q = 1) (hb : d361307 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43912, d361307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361441 q = 1) (hb : d363923 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361441, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d361441, d363923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361442 q = 1) (hb : d363924 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361442, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361442, d363924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d1578 q = 1) (hb : d361196 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1578, d361196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d361197 q = 1) (hb : d364514 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d361197, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d361197, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d361198 q = 1) (hb : d364515 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d361198, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361198, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361443 q = 1) (hb : d364522 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d361443, d364522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361443, d364522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100553 (p : Pattern) (ha : d361449 p = 1) (hb : d364533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361436 q = 1) (hb : d363948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361436, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100385 q ha hb
    | true =>
      simp only [d361436, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361437 q = 1) (hb : d363949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361437, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361437, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361438 q = 1) (hb : d363950 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361438, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361438, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361439 q = 1) (hb : d363951 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361439, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361439, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361311 q = 1) (hb : d364517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361311, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100550 q ha hb
    | true =>
      simp only [d361311, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361312 q = 1) (hb : d364518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361312, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361312, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361313 q = 1) (hb : d364519 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361313, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361313, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361314 q = 1) (hb : d364520 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361314, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361314, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361440 q = 1) (hb : d364521 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361440, d364521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361440, d364521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361444 q = 1) (hb : d364523 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
    | true =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361445 q = 1) (hb : d364524 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361446 q = 1) (hb : d364525 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361446, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361446, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361447 q = 1) (hb : d364526 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361447, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361447, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d361200 q = 1) (hb : d364528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
    | true =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361201 q = 1) (hb : d364529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361202 q = 1) (hb : d364530 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361202, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361202, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361203 q = 1) (hb : d364531 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361203, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361203, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361448 q = 1) (hb : d364532 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361448, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361448, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d361449 q = 1) (hb : d364533 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361449, d364533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361449, d364533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100554 (p : Pattern) (ha : d361564 p = 1) (hb : d364547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361450 q = 1) (hb : d364537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361450, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100553 q ha hb
    | true =>
      simp only [d361450, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100551 q ha hb
  have h2 (q : Pattern) (ha : d361451 q = 1) (hb : d364538 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361451, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361451, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361452 q = 1) (hb : d364539 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361452, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361452, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361317 q = 1) (hb : d364541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100551 q ha hb
    | true =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100549 q ha hb
  have h5 (q : Pattern) (ha : d361318 q = 1) (hb : d364542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361319 q = 1) (hb : d364543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361453 q = 1) (hb : d364544 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361453, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361453, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361562 q = 1) (hb : d364545 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361562, d364545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361562, d364545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361563 q = 1) (hb : d364546 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361563, d364546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361563, d364546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361564 q = 1) (hb : d364547 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361564, d364547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361564, d364547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100555 (p : Pattern) (ha : d361568 p = 1) (hb : d364551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361317 q = 1) (hb : d364541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100551 q ha hb
    | true =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100549 q ha hb
  have h2 (q : Pattern) (ha : d361318 q = 1) (hb : d364542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361319 q = 1) (hb : d364543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361562 q = 1) (hb : d364545 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361562, d364545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361562, d364545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361567 q = 1) (hb : d364550 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361567, d364550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361567, d364550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361568 q = 1) (hb : d364551 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361568, d364551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361568, d364551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100556 (p : Pattern) (ha : d361574 p = 1) (hb : d364557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361571 q = 1) (hb : d364554 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361572 q = 1) (hb : d364555 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361572, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361572, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361573 q = 1) (hb : d364556 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361573, d364556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361573, d364556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361574 q = 1) (hb : d364557 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361574, d364557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361574, d364557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100557 (p : Pattern) (ha : d361578 p = 1) (hb : d364561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361575 q = 1) (hb : d364558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361576 q = 1) (hb : d364559 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361576, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361576, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361577 q = 1) (hb : d364560 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361577, d364560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361577, d364560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361578 q = 1) (hb : d364561 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361578, d364561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361578, d364561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100558 (p : Pattern) (ha : d361584 p = 1) (hb : d364567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361579 q = 1) (hb : d364562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100556 q ha hb
    | true =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100557 q ha hb
  have h2 (q : Pattern) (ha : d361580 q = 1) (hb : d364563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361580, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361580, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361581 q = 1) (hb : d364564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361581, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361581, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361582 q = 1) (hb : d364565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361582, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361582, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361583 q = 1) (hb : d364566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361583, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361583, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361584 q = 1) (hb : d364567 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361584, d364567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361584, d364567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100559 (p : Pattern) (ha : d361587 p = 1) (hb : d364570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361571 q = 1) (hb : d364554 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361572 q = 1) (hb : d364555 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361572, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361572, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361573 q = 1) (hb : d364556 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361573, d364556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361573, d364556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361587 q = 1) (hb : d364570 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361587, d364570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361587, d364570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100560 (p : Pattern) (ha : d361588 p = 1) (hb : d364571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361575 q = 1) (hb : d364558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361576 q = 1) (hb : d364559 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361576, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361576, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361577 q = 1) (hb : d364560 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361577, d364560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361577, d364560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361588 q = 1) (hb : d364571 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361588, d364571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361588, d364571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100561 (p : Pattern) (ha : d361594 p = 1) (hb : d364577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361579 q = 1) (hb : d364562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100556 q ha hb
    | true =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100557 q ha hb
  have h2 (q : Pattern) (ha : d361580 q = 1) (hb : d364563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361580, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361580, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361581 q = 1) (hb : d364564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361581, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361581, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361582 q = 1) (hb : d364565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361582, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361582, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361583 q = 1) (hb : d364566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361583, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361583, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361589 q = 1) (hb : d364572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361589, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100559 q ha hb
    | true =>
      simp only [d361589, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100560 q ha hb
  have h7 (q : Pattern) (ha : d361590 q = 1) (hb : d364573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361590, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361590, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361591 q = 1) (hb : d364574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361591, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361591, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361592 q = 1) (hb : d364575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361592, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361592, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361593 q = 1) (hb : d364576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361593, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361593, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361594 q = 1) (hb : d364577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361594, d364577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361594, d364577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100562 (p : Pattern) (ha : d361599 p = 1) (hb : d364582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361571 q = 1) (hb : d364554 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361572 q = 1) (hb : d364555 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361572, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361572, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361598 q = 1) (hb : d364581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361598, d364581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361598, d364581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361599 q = 1) (hb : d364582 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361599, d364582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361599, d364582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100563 (p : Pattern) (ha : d361601 p = 1) (hb : d364584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361575 q = 1) (hb : d364558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361576 q = 1) (hb : d364559 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361576, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361576, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361600 q = 1) (hb : d364583 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361600, d364583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361600, d364583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361601 q = 1) (hb : d364584 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361601, d364584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361601, d364584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100564 (p : Pattern) (ha : d361608 p = 1) (hb : d364591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361571 q = 1) (hb : d364554 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361606 q = 1) (hb : d364589 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361606, d364589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361606, d364589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361607 q = 1) (hb : d364590 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361607, d364590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361607, d364590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361608 q = 1) (hb : d364591 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361608, d364591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361608, d364591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100565 (p : Pattern) (ha : d361611 p = 1) (hb : d364594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361575 q = 1) (hb : d364558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361609 q = 1) (hb : d364592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361609, d364592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361609, d364592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361610 q = 1) (hb : d364593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361610, d364593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361610, d364593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361611 q = 1) (hb : d364594 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361611, d364594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361611, d364594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100566 (p : Pattern) (ha : d361648 p = 1) (hb : d364599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361630 q = 1) (hb : d363919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361630, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100380 q ha hb
    | true =>
      simp only [d361630, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361631 q = 1) (hb : d363920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361631, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361631, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361632 q = 1) (hb : d363921 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361632, d363921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361632, d363921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361633 q = 1) (hb : d363922 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361633, d363922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361633, d363922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361635 q = 1) (hb : d363926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361635, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100381 q ha hb
    | true =>
      simp only [d361635, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361636 q = 1) (hb : d363927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361636, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361636, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361637 q = 1) (hb : d363928 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361637, d363928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361637, d363928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361638 q = 1) (hb : d363929 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361638, d363929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361638, d363929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361639 q = 1) (hb : d363930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361639, d363930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361639, d363930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361643 q = 1) (hb : d363934 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
    | true =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361644 q = 1) (hb : d363935 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361645 q = 1) (hb : d363936 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361645, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361645, d363936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361646 q = 1) (hb : d363937 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361646, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361646, d363937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d361444 q = 1) (hb : d364523 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
    | true =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361445 q = 1) (hb : d364524 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361446 q = 1) (hb : d364525 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361446, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361446, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361447 q = 1) (hb : d364526 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361447, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361447, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361647 q = 1) (hb : d364598 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361647, d364598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361647, d364598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d361648 q = 1) (hb : d364599 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361648, d364599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361648, d364599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100567 (p : Pattern) (ha : d361652 p = 1) (hb : d364603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361444 q = 1) (hb : d364523 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
    | true =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361445 q = 1) (hb : d364524 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361446 q = 1) (hb : d364525 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361446, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361446, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361447 q = 1) (hb : d364526 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361447, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361447, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361200 q = 1) (hb : d364528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
    | true =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361201 q = 1) (hb : d364529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361202 q = 1) (hb : d364530 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361202, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361202, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361203 q = 1) (hb : d364531 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361203, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361203, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361448 q = 1) (hb : d364532 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361448, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361448, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361204 q = 1) (hb : d364535 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361204, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361204, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361652 q = 1) (hb : d364603 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361652, d364603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361652, d364603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100568 (p : Pattern) (ha : d361658 p = 1) (hb : d364609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361649 q = 1) (hb : d364600 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361649, d364600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100566 q ha hb
    | true =>
      simp only [d361649, d364600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100553 q ha hb
  have h2 (q : Pattern) (ha : d361650 q = 1) (hb : d364601 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361650, d364601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361650, d364601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361651 q = 1) (hb : d364602 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361651, d364602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361651, d364602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361653 q = 1) (hb : d364604 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361653, d364604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100553 q ha hb
    | true =>
      simp only [d361653, d364604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100567 q ha hb
  have h5 (q : Pattern) (ha : d361654 q = 1) (hb : d364605 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361654, d364605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361654, d364605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361655 q = 1) (hb : d364606 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361655, d364606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361655, d364606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361656 q = 1) (hb : d364607 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361656, d364607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361656, d364607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361450 q = 1) (hb : d364537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361450, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100553 q ha hb
    | true =>
      simp only [d361450, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100551 q ha hb
  have h9 (q : Pattern) (ha : d361451 q = 1) (hb : d364538 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361451, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361451, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361452 q = 1) (hb : d364539 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361452, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361452, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361317 q = 1) (hb : d364541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100551 q ha hb
    | true =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100549 q ha hb
  have h12 (q : Pattern) (ha : d361318 q = 1) (hb : d364542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361319 q = 1) (hb : d364543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361453 q = 1) (hb : d364544 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361453, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361453, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361657 q = 1) (hb : d364608 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361657, d364608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361657, d364608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361658 q = 1) (hb : d364609 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361658, d364609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361658, d364609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100569 (p : Pattern) (ha : d361664 p = 1) (hb : d364615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361659 q = 1) (hb : d364610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361659, d364610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100568 q ha hb
    | true =>
      simp only [d361659, d364610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361660 q = 1) (hb : d364611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361660, d364611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361660, d364611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361661 q = 1) (hb : d364612 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361661, d364612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361661, d364612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361662 q = 1) (hb : d364613 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361662, d364613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361662, d364613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361663 q = 1) (hb : d364614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361663, d364614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361663, d364614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361664 q = 1) (hb : d364615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361664, d364615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361664, d364615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100570 (p : Pattern) (ha : d361670 p = 1) (hb : d364621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361667 q = 1) (hb : d364618 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361667, d364618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361667, d364618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361668 q = 1) (hb : d364619 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361668, d364619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361668, d364619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361669 q = 1) (hb : d364620 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361669, d364620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361669, d364620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361670 q = 1) (hb : d364621 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361670, d364621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361670, d364621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100571 (p : Pattern) (ha : d361676 p = 1) (hb : d364627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361602 q = 1) (hb : d364585 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361602, d364585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100562 q ha hb
    | true =>
      simp only [d361602, d364585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100563 q ha hb
  have h2 (q : Pattern) (ha : d361603 q = 1) (hb : d364586 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361603, d364586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361603, d364586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361604 q = 1) (hb : d364587 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361604, d364587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361604, d364587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361605 q = 1) (hb : d364588 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361605, d364588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361605, d364588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361612 q = 1) (hb : d364595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361612, d364595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100564 q ha hb
    | true =>
      simp only [d361612, d364595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100565 q ha hb
  have h6 (q : Pattern) (ha : d361613 q = 1) (hb : d364596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361613, d364596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361613, d364596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361614 q = 1) (hb : d364597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361614, d364597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361614, d364597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361665 q = 1) (hb : d364616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361665, d364616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100569 q ha hb
    | true =>
      simp only [d361665, d364616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100556 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361579 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d361666 q = 1) (hb : d364617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361666, d364617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361666, d364617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361671 q = 1) (hb : d364622 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361671, d364622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100570 q ha hb
    | true =>
      simp only [d361671, d364622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361672 q = 1) (hb : d364623 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361672, d364623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361672, d364623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361673 q = 1) (hb : d364624 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361673, d364624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361673, d364624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361674 q = 1) (hb : d364625 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361674, d364625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361674, d364625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361675 q = 1) (hb : d364626 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361675, d364626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361675, d364626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361676 q = 1) (hb : d364627 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361676, d364627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361676, d364627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro100572 (p : Pattern) (ha : d361677 p = 1) (hb : d364628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361571 q = 1) (hb : d364554 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361572 q = 1) (hb : d364555 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361572, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361572, d364555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361598 q = 1) (hb : d364581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361598, d364581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361598, d364581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361677 q = 1) (hb : d364628 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361677, d364628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361677, d364628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100573 (p : Pattern) (ha : d361678 p = 1) (hb : d364629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361575 q = 1) (hb : d364558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361576 q = 1) (hb : d364559 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361576, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361576, d364559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361600 q = 1) (hb : d364583 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361600, d364583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361600, d364583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361678 q = 1) (hb : d364629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361678, d364629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361678, d364629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100574 (p : Pattern) (ha : d361683 p = 1) (hb : d364634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361571 q = 1) (hb : d364554 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361571, d364554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361606 q = 1) (hb : d364589 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361606, d364589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361606, d364589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361607 q = 1) (hb : d364590 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361607, d364590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361607, d364590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361683 q = 1) (hb : d364634 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361683, d364634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361683, d364634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100575 (p : Pattern) (ha : d361684 p = 1) (hb : d364635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361569 q = 1) (hb : d364552 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100555 q ha hb
    | true =>
      simp only [d361569, d364552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361570 q = 1) (hb : d364553 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361570, d364553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361575 q = 1) (hb : d364558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361575, d364558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361609 q = 1) (hb : d364592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361609, d364592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361609, d364592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361610 q = 1) (hb : d364593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361610, d364593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361610, d364593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361684 q = 1) (hb : d364635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361684, d364635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361684, d364635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100576 (p : Pattern) (ha : d361688 p = 1) (hb : d364639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361659 q = 1) (hb : d364610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361659, d364610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100568 q ha hb
    | true =>
      simp only [d361659, d364610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361660 q = 1) (hb : d364611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361660, d364611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361660, d364611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361661 q = 1) (hb : d364612 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361661, d364612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361661, d364612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361662 q = 1) (hb : d364613 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361662, d364613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361662, d364613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361663 q = 1) (hb : d364614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361663, d364614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361663, d364614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361688 q = 1) (hb : d364639 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361688, d364639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361688, d364639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100577 (p : Pattern) (ha : d361691 p = 1) (hb : d364642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361565 q = 1) (hb : d364548 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100554 q ha hb
    | true =>
      simp only [d361565, d364548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361566 q = 1) (hb : d364549 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361566, d364549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361667 q = 1) (hb : d364618 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361667, d364618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361667, d364618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361668 q = 1) (hb : d364619 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361668, d364619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361668, d364619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361669 q = 1) (hb : d364620 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361669, d364620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361669, d364620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361691 q = 1) (hb : d364642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361691, d364642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361691, d364642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100578 (p : Pattern) (ha : d361697 p = 1) (hb : d364648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361602 q = 1) (hb : d364585 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361602, d364585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100562 q ha hb
    | true =>
      simp only [d361602, d364585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100563 q ha hb
  have h2 (q : Pattern) (ha : d361603 q = 1) (hb : d364586 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361603, d364586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361603, d364586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361604 q = 1) (hb : d364587 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361604, d364587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361604, d364587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361605 q = 1) (hb : d364588 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361605, d364588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361605, d364588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361612 q = 1) (hb : d364595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361612, d364595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100564 q ha hb
    | true =>
      simp only [d361612, d364595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100565 q ha hb
  have h6 (q : Pattern) (ha : d361613 q = 1) (hb : d364596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361613, d364596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361613, d364596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361614 q = 1) (hb : d364597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361614, d364597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361614, d364597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361665 q = 1) (hb : d364616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361665, d364616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100569 q ha hb
    | true =>
      simp only [d361665, d364616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100556 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361579 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d361666 q = 1) (hb : d364617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361666, d364617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361666, d364617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361671 q = 1) (hb : d364622 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361671, d364622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100570 q ha hb
    | true =>
      simp only [d361671, d364622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361672 q = 1) (hb : d364623 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361672, d364623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361672, d364623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361673 q = 1) (hb : d364624 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361673, d364624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361673, d364624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361674 q = 1) (hb : d364625 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361674, d364625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361674, d364625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361675 q = 1) (hb : d364626 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361675, d364626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361675, d364626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361679 q = 1) (hb : d364630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361679, d364630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100572 q ha hb
    | true =>
      simp only [d361679, d364630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100573 q ha hb
  have h17 (q : Pattern) (ha : d361680 q = 1) (hb : d364631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361680, d364631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361680, d364631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d361681 q = 1) (hb : d364632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361681, d364632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361681, d364632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d361682 q = 1) (hb : d364633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361682, d364633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361682, d364633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d361685 q = 1) (hb : d364636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361685, d364636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100574 q ha hb
    | true =>
      simp only [d361685, d364636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100575 q ha hb
  have h21 (q : Pattern) (ha : d361686 q = 1) (hb : d364637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361686, d364637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361686, d364637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d361687 q = 1) (hb : d364638 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361687, d364638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361687, d364638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d361689 q = 1) (hb : d364640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361689, d364640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100576 q ha hb
    | true =>
      simp only [d361689, d364640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100559 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d361589 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d361690 q = 1) (hb : d364641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361690, d364641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d361690, d364641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d361692 q = 1) (hb : d364643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361692, d364643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100577 q ha hb
    | true =>
      simp only [d361692, d364643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d361693 q = 1) (hb : d364644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361693, d364644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d361693, d364644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d361694 q = 1) (hb : d364645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361694, d364645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d361694, d364645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d361695 q = 1) (hb : d364646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361695, d364646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d361695, d364646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d361696 q = 1) (hb : d364647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361696, d364647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361696, d364647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d361697 q = 1) (hb : d364648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361697, d364648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361697, d364648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro100579 (p : Pattern) (ha : d361704 p = 1) (hb : d364655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361579 q = 1) (hb : d364562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100556 q ha hb
    | true =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100557 q ha hb
  have h2 (q : Pattern) (ha : d361580 q = 1) (hb : d364563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361580, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361580, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361581 q = 1) (hb : d364564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361581, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361581, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361582 q = 1) (hb : d364565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361582, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361582, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361583 q = 1) (hb : d364566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361583, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361583, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361699 q = 1) (hb : d364650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361699, d364650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100557 q ha hb
    | true =>
      simp only [d361699, d364650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361700 q = 1) (hb : d364651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361700, d364651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361700, d364651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361701 q = 1) (hb : d364652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361701, d364652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361701, d364652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361702 q = 1) (hb : d364653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361702, d364653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361702, d364653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361703 q = 1) (hb : d364654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361703, d364654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361703, d364654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361704 q = 1) (hb : d364655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361704, d364655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361704, d364655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100580 (p : Pattern) (ha : d361710 p = 1) (hb : d364661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361699 q = 1) (hb : d364650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361699, d364650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100557 q ha hb
    | true =>
      simp only [d361699, d364650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361700 q = 1) (hb : d364651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361700, d364651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361700, d364651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361701 q = 1) (hb : d364652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361701, d364652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361701, d364652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361702 q = 1) (hb : d364653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361702, d364653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361702, d364653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361703 q = 1) (hb : d364654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361703, d364654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361703, d364654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361705 q = 1) (hb : d364656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361705, d364656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100560 q ha hb
    | true =>
      simp only [d361705, d364656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361706 q = 1) (hb : d364657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361706, d364657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361706, d364657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361707 q = 1) (hb : d364658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361707, d364658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361707, d364658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361708 q = 1) (hb : d364659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361708, d364659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361708, d364659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361709 q = 1) (hb : d364660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361709, d364660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361709, d364660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361710 q = 1) (hb : d364661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361710, d364661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361710, d364661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100581 (p : Pattern) (ha : d361717 p = 1) (hb : d364668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361689 q = 1) (hb : d364640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361689, d364640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100576 q ha hb
    | true =>
      simp only [d361689, d364640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100559 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361690 q = 1) (hb : d364641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361690, d364641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361690, d364641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d361692 q = 1) (hb : d364643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361692, d364643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100577 q ha hb
    | true =>
      simp only [d361692, d364643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361693 q = 1) (hb : d364644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361693, d364644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361693, d364644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361694 q = 1) (hb : d364645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361694, d364645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361694, d364645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361715 q = 1) (hb : d364666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361715, d364666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361715, d364666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361716 q = 1) (hb : d364667 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361716, d364667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361716, d364667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361717 q = 1) (hb : d364668 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361717, d364668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361717, d364668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100582 (p : Pattern) (ha : d361719 p = 1) (hb : d364670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361705 q = 1) (hb : d364656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361705, d364656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100560 q ha hb
    | true =>
      simp only [d361705, d364656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361706 q = 1) (hb : d364657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361706, d364657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361706, d364657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361707 q = 1) (hb : d364658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361707, d364658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361707, d364658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361708 q = 1) (hb : d364659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361708, d364659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361708, d364659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361709 q = 1) (hb : d364660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361709, d364660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361709, d364660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361719 q = 1) (hb : d364670 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361719, d364670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361719, d364670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100583 (p : Pattern) (ha : d361246 p = 1) (hb : d364707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361241 q = 1) (hb : d364687 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361241, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361241, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
  have h2 (q : Pattern) (ha : d361200 q = 1) (hb : d364528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
    | true =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361242 q = 1) (hb : d364688 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361242, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361242, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361201 q = 1) (hb : d364529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361243 q = 1) (hb : d364689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361243, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361243, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361244 q = 1) (hb : d364690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361244, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361244, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361245 q = 1) (hb : d364696 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361245, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361245, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361246 q = 1) (hb : d364707 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361246, d364707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361246, d364707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100584 (p : Pattern) (ha : d361370 p = 1) (hb : d364703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361365 q = 1) (hb : d364682 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361365, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361365, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100550 q ha hb
  have h2 (q : Pattern) (ha : d361311 q = 1) (hb : d364517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361311, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100550 q ha hb
    | true =>
      simp only [d361311, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361366 q = 1) (hb : d364683 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361366, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361366, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361312 q = 1) (hb : d364518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361312, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361312, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361367 q = 1) (hb : d364684 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361367, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361367, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361368 q = 1) (hb : d364685 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361368, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361368, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361241 q = 1) (hb : d364687 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361241, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361241, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
  have h8 (q : Pattern) (ha : d361200 q = 1) (hb : d364528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
    | true =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361242 q = 1) (hb : d364688 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361242, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361242, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361201 q = 1) (hb : d364529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361243 q = 1) (hb : d364689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361243, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361243, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d361244 q = 1) (hb : d364690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361244, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361244, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361369 q = 1) (hb : d364702 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361369, d364702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361369, d364702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361245 q = 1) (hb : d364696 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361245, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361245, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361370 q = 1) (hb : d364703 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361370, d364703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361370, d364703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100585 (p : Pattern) (ha : d361519 p = 1) (hb : d364692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361509 q = 1) (hb : d364160 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361509, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361509, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100385 q ha hb
  have h2 (q : Pattern) (ha : d361436 q = 1) (hb : d363948 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361436, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100385 q ha hb
    | true =>
      simp only [d361436, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361510 q = 1) (hb : d364161 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361510, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361510, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361437 q = 1) (hb : d363949 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361437, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361437, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361511 q = 1) (hb : d364162 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361511, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361511, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361512 q = 1) (hb : d364163 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361512, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361512, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361365 q = 1) (hb : d364682 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361365, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361365, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100550 q ha hb
  have h8 (q : Pattern) (ha : d361311 q = 1) (hb : d364517 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361311, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100550 q ha hb
    | true =>
      simp only [d361311, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361366 q = 1) (hb : d364683 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361366, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361366, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361312 q = 1) (hb : d364518 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361312, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361312, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361367 q = 1) (hb : d364684 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361367, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361367, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d361368 q = 1) (hb : d364685 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361368, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361368, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361513 q = 1) (hb : d364686 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361513, d364686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361513, d364686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361514 q = 1) (hb : d364676 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361514, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361514, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
  have h15 (q : Pattern) (ha : d361444 q = 1) (hb : d364523 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
    | true =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361515 q = 1) (hb : d364677 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361515, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361515, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361445 q = 1) (hb : d364524 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361516 q = 1) (hb : d364678 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361516, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361516, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d361517 q = 1) (hb : d364679 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361517, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d361517, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d361241 q = 1) (hb : d364687 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361241, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361241, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
  have h21 (q : Pattern) (ha : d361200 q = 1) (hb : d364528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
    | true =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d361242 q = 1) (hb : d364688 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361242, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d361242, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d361201 q = 1) (hb : d364529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d361243 q = 1) (hb : d364689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361243, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d361243, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d361244 q = 1) (hb : d364690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361244, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d361244, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d361518 q = 1) (hb : d364691 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361518, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361518, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d361519 q = 1) (hb : d364692 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361519, d364692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361519, d364692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100586 (p : Pattern) (ha : d361739 p = 1) (hb : d364681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361725 q = 1) (hb : d364136 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361725, d364136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361725, d364136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100380 q ha hb
  have h2 (q : Pattern) (ha : d361630 q = 1) (hb : d363919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361630, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100380 q ha hb
    | true =>
      simp only [d361630, d363919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361726 q = 1) (hb : d364137 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361726, d364137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361726, d364137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361631 q = 1) (hb : d363920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361631, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361631, d363920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361727 q = 1) (hb : d364138 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361727, d364138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361727, d364138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361728 q = 1) (hb : d364139 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361728, d364139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361728, d364139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361729 q = 1) (hb : d364140 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361729, d364140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361729, d364140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100381 q ha hb
  have h8 (q : Pattern) (ha : d361635 q = 1) (hb : d363926 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361635, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100381 q ha hb
    | true =>
      simp only [d361635, d363926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361730 q = 1) (hb : d364141 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361730, d364141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361730, d364141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361636 q = 1) (hb : d363927 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361636, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361636, d363927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361731 q = 1) (hb : d364142 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361731, d364142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361731, d364142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d361732 q = 1) (hb : d364143 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361732, d364143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361732, d364143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361733 q = 1) (hb : d364144 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361733, d364144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361733, d364144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361734 q = 1) (hb : d364130 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361734, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361734, d364130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
  have h15 (q : Pattern) (ha : d361643 q = 1) (hb : d363934 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100382 q ha hb
    | true =>
      simp only [d361643, d363934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361735 q = 1) (hb : d364131 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361735, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361735, d364131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361644 q = 1) (hb : d363935 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361644, d363935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d361736 q = 1) (hb : d364132 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361736, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361736, d364132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d361737 q = 1) (hb : d364133 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361737, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d361737, d364133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d361514 q = 1) (hb : d364676 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361514, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361514, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
  have h21 (q : Pattern) (ha : d361444 q = 1) (hb : d364523 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
    | true =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d361515 q = 1) (hb : d364677 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361515, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d361515, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d361445 q = 1) (hb : d364524 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d361516 q = 1) (hb : d364678 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361516, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d361516, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d361517 q = 1) (hb : d364679 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361517, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d361517, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d361738 q = 1) (hb : d364680 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361738, d364680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361738, d364680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d361739 q = 1) (hb : d364681 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361739, d364681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361739, d364681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100587 (p : Pattern) (ha : d361743 p = 1) (hb : d364697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361514 q = 1) (hb : d364676 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361514, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361514, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
  have h2 (q : Pattern) (ha : d361444 q = 1) (hb : d364523 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100552 q ha hb
    | true =>
      simp only [d361444, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361515 q = 1) (hb : d364677 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361515, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361515, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361445 q = 1) (hb : d364524 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361445, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361516 q = 1) (hb : d364678 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361516, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361516, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361517 q = 1) (hb : d364679 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361517, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361517, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361241 q = 1) (hb : d364687 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361241, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361241, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
  have h8 (q : Pattern) (ha : d361200 q = 1) (hb : d364528 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100548 q ha hb
    | true =>
      simp only [d361200, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361242 q = 1) (hb : d364688 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361242, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361242, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361201 q = 1) (hb : d364529 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361201, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d361243 q = 1) (hb : d364689 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d361243, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361243, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d361244 q = 1) (hb : d364690 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d361244, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361244, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361518 q = 1) (hb : d364691 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361518, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361518, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361245 q = 1) (hb : d364696 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d361245, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361245, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361743 q = 1) (hb : d364697 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d361743, d364697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361743, d364697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100588 (p : Pattern) (ha : d361749 p = 1) (hb : d364713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361740 q = 1) (hb : d364693 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361740, d364693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100586 q ha hb
    | true =>
      simp only [d361740, d364693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100585 q ha hb
  have h2 (q : Pattern) (ha : d361741 q = 1) (hb : d364694 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361741, d364694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361741, d364694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361742 q = 1) (hb : d364695 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361742, d364695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361742, d364695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361744 q = 1) (hb : d364698 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361744, d364698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100585 q ha hb
    | true =>
      simp only [d361744, d364698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100587 q ha hb
  have h5 (q : Pattern) (ha : d361745 q = 1) (hb : d364699 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361745, d364699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361745, d364699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361746 q = 1) (hb : d364700 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361746, d364700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361746, d364700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361747 q = 1) (hb : d364701 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361747, d364701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361747, d364701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361520 q = 1) (hb : d364704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361520, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100585 q ha hb
    | true =>
      simp only [d361520, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100584 q ha hb
  have h9 (q : Pattern) (ha : d361521 q = 1) (hb : d364705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361521, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361521, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361522 q = 1) (hb : d364706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361522, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361522, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361371 q = 1) (hb : d364708 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100584 q ha hb
    | true =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100583 q ha hb
  have h12 (q : Pattern) (ha : d361372 q = 1) (hb : d364709 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361373 q = 1) (hb : d364710 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361523 q = 1) (hb : d364711 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361523, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361523, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361748 q = 1) (hb : d364712 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361748, d364712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361748, d364712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361749 q = 1) (hb : d364713 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361749, d364713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361749, d364713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100589 (p : Pattern) (ha : d361754 p = 1) (hb : d364718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361520 q = 1) (hb : d364704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361520, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100585 q ha hb
    | true =>
      simp only [d361520, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100584 q ha hb
  have h2 (q : Pattern) (ha : d361521 q = 1) (hb : d364705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361521, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361521, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361522 q = 1) (hb : d364706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361522, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361522, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361371 q = 1) (hb : d364708 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100584 q ha hb
    | true =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100583 q ha hb
  have h5 (q : Pattern) (ha : d361372 q = 1) (hb : d364709 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361373 q = 1) (hb : d364710 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361523 q = 1) (hb : d364711 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361523, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361523, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361752 q = 1) (hb : d364716 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361752, d364716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361752, d364716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361753 q = 1) (hb : d364717 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361753, d364717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361753, d364717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361754 q = 1) (hb : d364718 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361754, d364718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361754, d364718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100590 (p : Pattern) (ha : d361760 p = 1) (hb : d364724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361750 q = 1) (hb : d364714 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361750, d364714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100588 q ha hb
    | true =>
      simp only [d361750, d364714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361751 q = 1) (hb : d364715 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361751, d364715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361751, d364715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361755 q = 1) (hb : d364719 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361755, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100589 q ha hb
    | true =>
      simp only [d361755, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361756 q = 1) (hb : d364720 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361756, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361756, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361757 q = 1) (hb : d364721 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361757, d364721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361757, d364721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361758 q = 1) (hb : d364722 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361758, d364722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361758, d364722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361759 q = 1) (hb : d364723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361759, d364723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361759, d364723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361760 q = 1) (hb : d364724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361760, d364724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361760, d364724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100591 (p : Pattern) (ha : d361762 p = 1) (hb : d364726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361371 q = 1) (hb : d364708 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100584 q ha hb
    | true =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100583 q ha hb
  have h2 (q : Pattern) (ha : d361372 q = 1) (hb : d364709 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361373 q = 1) (hb : d364710 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361752 q = 1) (hb : d364716 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361752, d364716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361752, d364716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361761 q = 1) (hb : d364725 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361761, d364725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361761, d364725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361762 q = 1) (hb : d364726 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361762, d364726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361762, d364726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100592 (p : Pattern) (ha : d361768 p = 1) (hb : d364732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361755 q = 1) (hb : d364719 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361755, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100589 q ha hb
    | true =>
      simp only [d361755, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361756 q = 1) (hb : d364720 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361756, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361756, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361763 q = 1) (hb : d364727 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361763, d364727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100591 q ha hb
    | true =>
      simp only [d361763, d364727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361764 q = 1) (hb : d364728 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361764, d364728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361764, d364728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361765 q = 1) (hb : d364729 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361765, d364729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361765, d364729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361766 q = 1) (hb : d364730 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361766, d364730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361766, d364730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361767 q = 1) (hb : d364731 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361767, d364731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361767, d364731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361768 q = 1) (hb : d364732 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361768, d364732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361768, d364732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100593 (p : Pattern) (ha : d361779 p = 1) (hb : d364738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361755 q = 1) (hb : d364719 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361755, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100589 q ha hb
    | true =>
      simp only [d361755, d364719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361756 q = 1) (hb : d364720 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361756, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361756, d364720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361776 q = 1) (hb : d364735 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361776, d364735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361776, d364735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361777 q = 1) (hb : d364736 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361777, d364736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361777, d364736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361778 q = 1) (hb : d364737 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361778, d364737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361778, d364737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361779 q = 1) (hb : d364738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361779, d364738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361779, d364738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100594 (p : Pattern) (ha : d361785 p = 1) (hb : d364744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361769 q = 1) (hb : d364733 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361769, d364733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100590 q ha hb
    | true =>
      simp only [d361769, d364733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100592 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361774 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361775 q = 1) (hb : d364734 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361775, d364734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361775, d364734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d361780 q = 1) (hb : d364739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361780, d364739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100593 q ha hb
    | true =>
      simp only [d361780, d364739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361781 q = 1) (hb : d364740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361781, d364740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361781, d364740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361782 q = 1) (hb : d364741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361782, d364741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361782, d364741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361783 q = 1) (hb : d364742 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361783, d364742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361783, d364742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361784 q = 1) (hb : d364743 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361784, d364743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361784, d364743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361785 q = 1) (hb : d364744 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361785, d364744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361785, d364744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100595 (p : Pattern) (ha : d361773 p = 1) (hb : d364749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361763 q = 1) (hb : d364727 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361763, d364727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100591 q ha hb
    | true =>
      simp only [d361763, d364727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361764 q = 1) (hb : d364728 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361764, d364728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361764, d364728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361770 q = 1) (hb : d364746 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361770, d364746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361770, d364746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361771 q = 1) (hb : d364747 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361771, d364747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361771, d364747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361772 q = 1) (hb : d364748 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361772, d364748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361772, d364748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361773 q = 1) (hb : d364749 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361773, d364749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361773, d364749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100596 (p : Pattern) (ha : d361792 p = 1) (hb : d364755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361787 q = 1) (hb : d364750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361787, d364750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100595 q ha hb
    | true =>
      simp only [d361787, d364750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361788 q = 1) (hb : d364751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361788, d364751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361788, d364751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361789 q = 1) (hb : d364752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361789, d364752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361789, d364752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361790 q = 1) (hb : d364753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361790, d364753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361790, d364753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361791 q = 1) (hb : d364754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361791, d364754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361791, d364754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361792 q = 1) (hb : d364755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361792, d364755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361792, d364755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100597 (p : Pattern) (ha : d361798 p = 1) (hb : d364761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361585 q = 1) (hb : d364568 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361585, d364568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361585, d364568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100558 q ha hb
  have h2 (q : Pattern) (ha : d361586 q = 1) (hb : d364569 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361586, d364569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361586, d364569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361595 q = 1) (hb : d364578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361595, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100558 q ha hb
    | true =>
      simp only [d361595, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100561 q ha hb
  have h4 (q : Pattern) (ha : d361596 q = 1) (hb : d364579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361596, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361596, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361597 q = 1) (hb : d364580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361597, d364580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361597, d364580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361698 q = 1) (hb : d364649 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361698, d364649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100571 q ha hb
    | true =>
      simp only [d361698, d364649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100578 q ha hb
  have h7 (q : Pattern) (ha : d361711 q = 1) (hb : d364662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361711, d364662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100579 q ha hb
    | true =>
      simp only [d361711, d364662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100580 q ha hb
  have h8 (q : Pattern) (ha : d361712 q = 1) (hb : d364663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361712, d364663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361712, d364663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361713 q = 1) (hb : d364664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361713, d364664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361713, d364664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d361714 q = 1) (hb : d364665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361714, d364665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361714, d364665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361718 q = 1) (hb : d364669 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361718, d364669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361718, d364669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100581 q ha hb
  have h12 (q : Pattern) (ha : d361720 q = 1) (hb : d364671 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361720, d364671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361720, d364671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100582 q ha hb
  have h13 (q : Pattern) (ha : d361721 q = 1) (hb : d364672 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361721, d364672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361721, d364672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361722 q = 1) (hb : d364673 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361722, d364673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361722, d364673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361723 q = 1) (hb : d364674 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361723, d364674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361723, d364674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361724 q = 1) (hb : d364675 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361724, d364675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361724, d364675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361786 q = 1) (hb : d364745 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361786, d364745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361786, d364745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100594 q ha hb
  have h18 (q : Pattern) (ha : d361793 q = 1) (hb : d364756 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361793, d364756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361793, d364756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100596 q ha hb
  have h19 (q : Pattern) (ha : d361794 q = 1) (hb : d364757 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361794, d364757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361794, d364757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d361795 q = 1) (hb : d364758 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361795, d364758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361795, d364758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d361796 q = 1) (hb : d364759 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361796, d364759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d361796, d364759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d361797 q = 1) (hb : d364760 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361797, d364760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361797, d364760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d361798 q = 1) (hb : d364761 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d361798, d364761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361798, d364761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100598 (p : Pattern) (ha : d361804 p = 1) (hb : d364767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361799 q = 1) (hb : d364762 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d361799, d364762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361799, d364762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100597 q ha hb
  have h2 (q : Pattern) (ha : d361800 q = 1) (hb : d364763 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d361800, d364763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361800, d364763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361801 q = 1) (hb : d364764 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d361801, d364764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361801, d364764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361802 q = 1) (hb : d364765 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d361802, d364765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361802, d364765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361803 q = 1) (hb : d364766 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d361803, d364766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361803, d364766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361804 q = 1) (hb : d364767 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d361804, d364767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361804, d364767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100599 (p : Pattern) (ha : d364471 p = 1) (hb : d364773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361805 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361805 q = 1) (hb : d364768 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d361805, d364768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361805, d364768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100598 q ha hb
  have h3 (q : Pattern) (ha : d361805 q = 1) (hb : d364769 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d364769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d364769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d364468 q = 1) (hb : d364770 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364468, d364770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364468, d364770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d364469 q = 1) (hb : d364771 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d364469, d364771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364469, d364771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d364470 q = 1) (hb : d364772 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d364470, d364772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d364470, d364772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d364471 q = 1) (hb : d364773 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d364471, d364773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d364471, d364773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro100600 (p : Pattern) (ha : d364477 p = 1) (hb : d364779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364472 q = 1) (hb : d364774 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d364472, d364774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100599 q ha hb
    | true =>
      simp only [d364472, d364774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364473 q = 1) (hb : d364775 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d364473, d364775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364473, d364775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364474 q = 1) (hb : d364776 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d364474, d364776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364474, d364776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364475 q = 1) (hb : d364777 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d364475, d364777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364475, d364777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364476 q = 1) (hb : d364778 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d364476, d364778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364476, d364778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364477 q = 1) (hb : d364779 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d364477, d364779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364477, d364779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100601 (p : Pattern) (ha : d364483 p = 1) (hb : d364785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364478 q = 1) (hb : d364780 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d364478, d364780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100600 q ha hb
    | true =>
      simp only [d364478, d364780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364479 q = 1) (hb : d364781 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d364479, d364781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364479, d364781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364480 q = 1) (hb : d364782 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d364480, d364782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364480, d364782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364481 q = 1) (hb : d364783 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d364481, d364783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364481, d364783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364482 q = 1) (hb : d364784 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d364482, d364784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364482, d364784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364483 q = 1) (hb : d364785 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d364483, d364785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364483, d364785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100602 (p : Pattern) (ha : d364489 p = 1) (hb : d364791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364484 q = 1) (hb : d364786 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d364484, d364786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100601 q ha hb
    | true =>
      simp only [d364484, d364786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364485 q = 1) (hb : d364787 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d364485, d364787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364485, d364787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364486 q = 1) (hb : d364788 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d364486, d364788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364486, d364788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364487 q = 1) (hb : d364789 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d364487, d364789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364487, d364789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364488 q = 1) (hb : d364790 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d364488, d364790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364488, d364790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364489 q = 1) (hb : d364791 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d364489, d364791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364489, d364791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100603 (p : Pattern) (ha : d364495 p = 1) (hb : d364797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364490 q = 1) (hb : d364792 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d364490, d364792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100602 q ha hb
    | true =>
      simp only [d364490, d364792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364491 q = 1) (hb : d364793 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d364491, d364793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364491, d364793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364492 q = 1) (hb : d364794 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d364492, d364794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364492, d364794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364493 q = 1) (hb : d364795 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d364493, d364795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364493, d364795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364494 q = 1) (hb : d364796 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d364494, d364796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364494, d364796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364495 q = 1) (hb : d364797 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d364495, d364797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364495, d364797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100604 (p : Pattern) (ha : d364501 p = 1) (hb : d364803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364496 q = 1) (hb : d364798 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d364496, d364798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100603 q ha hb
    | true =>
      simp only [d364496, d364798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364497 q = 1) (hb : d364799 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d364497, d364799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364497, d364799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364498 q = 1) (hb : d364800 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d364498, d364800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364498, d364800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364499 q = 1) (hb : d364801 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d364499, d364801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364499, d364801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364500 q = 1) (hb : d364802 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d364500, d364802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364500, d364802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364501 q = 1) (hb : d364803 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d364501, d364803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364501, d364803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100605 (p : Pattern) (ha : d364507 p = 1) (hb : d364809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364502 q = 1) (hb : d364804 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d364502, d364804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100604 q ha hb
    | true =>
      simp only [d364502, d364804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364503 q = 1) (hb : d364805 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d364503, d364805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364503, d364805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364504 q = 1) (hb : d364806 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d364504, d364806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364504, d364806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364505 q = 1) (hb : d364807 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d364505, d364807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364505, d364807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364506 q = 1) (hb : d364808 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d364506, d364808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364506, d364808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364507 q = 1) (hb : d364809 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d364507, d364809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364507, d364809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100606 (p : Pattern) (ha : d364513 p = 1) (hb : d364815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364508 q = 1) (hb : d364810 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d364508, d364810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100605 q ha hb
    | true =>
      simp only [d364508, d364810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364509 q = 1) (hb : d364811 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d364509, d364811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364509, d364811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364510 q = 1) (hb : d364812 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d364510, d364812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364510, d364812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364511 q = 1) (hb : d364813 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d364511, d364813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364511, d364813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364512 q = 1) (hb : d364814 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d364512, d364814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364512, d364814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364513 q = 1) (hb : d364815 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d364513, d364815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364513, d364815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100607 (p : Pattern) (ha : d308 p = 1) (hb : d357470 p = 1) : d364818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42909 q = 1) : d364572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42909, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100497 q ha hb
    | true =>
      simp only [d42909, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100498 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42910 q = 1) : d364573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42910, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42910, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42911 q = 1) : d364574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42911, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42911, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42912 q = 1) : d364575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42912, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42912, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42913 q = 1) : d364576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42913, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42913, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357470 q = 1) : d364818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357470, d364818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357470, d364818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100608 (p : Pattern) (ha : d308 p = 1) (hb : d357481 p = 1) : d364829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d357476 q = 1) : d364824 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d357476, d364824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100535 q ha hb
    | true =>
      simp only [d357476, d364824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100506 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357477 q = 1) : d364825 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d357477, d364825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357477, d364825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357478 q = 1) : d364826 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d357478, d364826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357478, d364826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357479 q = 1) : d364827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d357479, d364827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357479, d364827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357480 q = 1) : d364828 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d357480, d364828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357480, d364828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357481 q = 1) : d364829 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d357481, d364829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357481, d364829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100609 (p : Pattern) (ha : d308 p = 1) (hb : d357487 p = 1) : d364835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42915 q = 1) : d364578 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42915, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100496 q ha hb
    | true =>
      simp only [d42915, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100499 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42916 q = 1) : d364579 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42916, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42916, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357468 q = 1) : d364816 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357468, d364816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357468, d364816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357469 q = 1) : d364817 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357469, d364817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357469, d364817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357471 q = 1) : d364819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357471, d364819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357471, d364819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100607 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357472 q = 1) : d364820 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357472, d364820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357472, d364820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d357473 q = 1) : d364821 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357473, d364821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d357473, d364821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d357474 q = 1) : d364822 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357474, d364822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357474, d364822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d357475 q = 1) : d364823 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357475, d364823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357475, d364823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d357482 q = 1) : d364830 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d357482, d364830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357482, d364830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100608 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d357483 q = 1) : d364831 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d357483, d364831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d357483, d364831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d357484 q = 1) : d364832 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d357484, d364832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d357484, d364832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d357485 q = 1) : d364833 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d357485, d364833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d357485, d364833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d357486 q = 1) : d364834 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d357486, d364834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d357486, d364834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d357487 q = 1) : d364835 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d357487, d364835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357487, d364835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100610 (p : Pattern) (ha : d308 p = 1) (hb : d357493 p = 1) : d364841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d357488 q = 1) : d364836 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d357488, d364836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357488, d364836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100609 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357489 q = 1) : d364837 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d357489, d364837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357489, d364837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d357490 q = 1) : d364838 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d357490, d364838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357490, d364838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d357491 q = 1) : d364839 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d357491, d364839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357491, d364839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d357492 q = 1) : d364840 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d357492, d364840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357492, d364840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d357493 q = 1) : d364841 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357493, d364841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357493, d364841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100611 (p : Pattern) (ha : d357556 p = 1) (hb : d364416 p = 1) : d364847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d357494 q = 1) : d364842 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357494, d364842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d357494, d364842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100610 q ha hb
  have h3 (q : Pattern) (ha : d357495 q = 1) (hb : d364413 q = 1) : d364843 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d364413, d364843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d357495, d364413, d364843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357524 q = 1) (hb : d364414 q = 1) : d364844 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d364414, d364844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d364414, d364844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357554 q = 1) (hb : d364415 q = 1) : d364845 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d364415, d364845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357554, d364415, d364845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357555 q = 1) (hb : d364416 q = 1) : d364846 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d364416, d364846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357555, d364416, d364846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d364416 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d357556 q = 1) (hb : d364416 q = 1) : d364847 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d364847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357556, d364847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100612 (p : Pattern) (ha : d357562 p = 1) (hb : d364416 p = 1) : d364853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364416 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d364416 q = 1) : d364848 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d364848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100611 q ha hb
    | true =>
      simp only [d357557, d364848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d364416 q = 1) : d364849 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d364849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d364849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d364416 q = 1) : d364850 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d364850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d364850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357560 q = 1) (hb : d364416 q = 1) : d364851 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d364851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d364851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357561 q = 1) (hb : d364416 q = 1) : d364852 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d364852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d364852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357562 q = 1) (hb : d364416 q = 1) : d364853 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d364853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d364853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100613 (p : Pattern) (ha : d357568 p = 1) (hb : d364421 p = 1) : d364859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d364417 q = 1) : d364854 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d364417, d364854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100612 q ha hb
    | true =>
      simp only [d357563, d364417, d364854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d364418 q = 1) : d364855 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d364418, d364855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d364418, d364855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d364419 q = 1) : d364856 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d364419, d364856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d364419, d364856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357566 q = 1) (hb : d364420 q = 1) : d364857 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d364420, d364857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d364420, d364857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357567 q = 1) (hb : d364421 q = 1) : d364858 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d364421, d364858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d364421, d364858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357568 q = 1) (hb : d364421 q = 1) : d364859 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, d364859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, d364859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100614 (p : Pattern) (ha : d357574 p = 1) (hb : d364421 p = 1) : d364865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d364421 q = 1) : d364860 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, d364860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100613 q ha hb
    | true =>
      simp only [d357569, d364860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d364421 q = 1) : d364861 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, d364861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, d364861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d364421 q = 1) : d364862 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, d364862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, d364862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d364421 q = 1) : d364863 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, d364863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, d364863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d364421 q = 1) : d364864 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, d364864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, d364864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d364421 q = 1) : d364865 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, d364865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, d364865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100615 (p : Pattern) (ha : d357580 p = 1) (hb : d364421 p = 1) : d364871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d364421 q = 1) : d364866 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, d364866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100614 q ha hb
    | true =>
      simp only [d357575, d364866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d364421 q = 1) : d364867 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, d364867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, d364867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d364421 q = 1) : d364868 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, d364868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, d364868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d364421 q = 1) : d364869 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, d364869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, d364869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d364421 q = 1) : d364870 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, d364870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, d364870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d364421 q = 1) : d364871 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, d364871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, d364871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100616 (p : Pattern) (ha : d357586 p = 1) (hb : d364421 p = 1) : d364877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d364421 q = 1) : d364872 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, d364872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100615 q ha hb
    | true =>
      simp only [d357581, d364872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d364421 q = 1) : d364873 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, d364873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, d364873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d364421 q = 1) : d364874 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, d364874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, d364874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d364421 q = 1) : d364875 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, d364875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, d364875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d364421 q = 1) : d364876 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, d364876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, d364876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d364421 q = 1) : d364877 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, d364877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, d364877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100617 (p : Pattern) (ha : d357592 p = 1) (hb : d364421 p = 1) : d364883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d364421 q = 1) : d364878 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, d364878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100616 q ha hb
    | true =>
      simp only [d357587, d364878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d364421 q = 1) : d364879 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, d364879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, d364879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d364421 q = 1) : d364880 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, d364880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, d364880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d364421 q = 1) : d364881 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, d364881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, d364881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d364421 q = 1) : d364882 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, d364882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, d364882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d364421 q = 1) : d364883 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, d364883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, d364883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100618 (p : Pattern) (ha : d357598 p = 1) (hb : d364421 p = 1) : d364889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364421 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d364421 q = 1) : d364884 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, d364884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100617 q ha hb
    | true =>
      simp only [d357593, d364884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d364421 q = 1) : d364885 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, d364885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, d364885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d364421 q = 1) : d364886 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, d364886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, d364886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d364421 q = 1) : d364887 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, d364887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, d364887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d364421 q = 1) : d364888 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, d364888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, d364888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d364421 q = 1) : d364889 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, d364889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, d364889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100619 (p : Pattern) (ha : d361676 p = 1) (hb : d364567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361614 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d361665 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d361579 q = 1) (hb : d364562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100556 q ha hb
    | true =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100557 q ha hb
  have h5 (q : Pattern) (ha : d361666 q = 1) (hb : d364563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361666, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d361666, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d361672 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d361673 q = 1) (hb : d364564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361673, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361673, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d361674 q = 1) (hb : d364565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361674, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361674, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361675 q = 1) (hb : d364566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361675, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361675, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361676 q = 1) (hb : d364567 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361676, d364567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361676, d364567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100620 (p : Pattern) (ha : d361697 p = 1) (hb : d364577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361605 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361614 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361665 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361579 q = 1) (hb : d364562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100556 q ha hb
    | true =>
      simp only [d361579, d364562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100557 q ha hb
  have h4 (q : Pattern) (ha : d361666 q = 1) (hb : d364563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361666, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d361666, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d361672 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d361673 q = 1) (hb : d364564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361673, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361673, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d361674 q = 1) (hb : d364565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361674, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361674, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361675 q = 1) (hb : d364566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361675, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361675, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361682 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d361687 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d361689 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d361589 q = 1) (hb : d364572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361589, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100559 q ha hb
    | true =>
      simp only [d361589, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100560 q ha hb
  have h13 (q : Pattern) (ha : d361690 q = 1) (hb : d364573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361690, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d361690, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d361693 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d361694 q = 1) (hb : d364574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361694, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361694, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d361695 q = 1) (hb : d364575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361695, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d361695, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361696 q = 1) (hb : d364576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361696, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d361696, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d361697 q = 1) (hb : d364577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361697, d364577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361697, d364577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100621 (p : Pattern) (ha : d361717 p = 1) (hb : d364818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361689 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361589 q = 1) (hb : d364572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361589, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100559 q ha hb
    | true =>
      simp only [d361589, d364572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100560 q ha hb
  have h3 (q : Pattern) (ha : d361690 q = 1) (hb : d364573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361690, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361690, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361693 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361694 q = 1) (hb : d364574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361694, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361694, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361715 q = 1) (hb : d364575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361715, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361715, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361716 q = 1) (hb : d364576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361716, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361716, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361717 q = 1) (hb : d364818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361717, d364818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361717, d364818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100622 (p : Pattern) (ha : d361785 p = 1) (hb : d364829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361774 q = 1) (hb : d364824 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361774, d364824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100592 q ha hb
    | true =>
      simp only [d361774, d364824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100595 q ha hb
  have h3 (q : Pattern) (ha : d361775 q = 1) (hb : d364825 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361775, d364825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361775, d364825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d361781 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361782 q = 1) (hb : d364826 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361782, d364826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361782, d364826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361783 q = 1) (hb : d364827 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361783, d364827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361783, d364827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361784 q = 1) (hb : d364828 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361784, d364828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361784, d364828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361785 q = 1) (hb : d364829 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361785, d364829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361785, d364829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100623 (p : Pattern) (ha : d361798 p = 1) (hb : d364835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361597 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361698 q = 1) (hb : d364578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361698, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100619 q ha hb
    | true =>
      simp only [d361698, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100620 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361712 q = 1) (hb : d364579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361712, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361712, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d361713 q = 1) (hb : d364816 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361713, d364816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361713, d364816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d361714 q = 1) (hb : d364817 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361714, d364817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361714, d364817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361718 q = 1) (hb : d364819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361718, d364819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d361718, d364819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100621 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d361720 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d361721 q = 1) (hb : d364820 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361721, d364820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361721, d364820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d361722 q = 1) (hb : d364821 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361722, d364821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361722, d364821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d361723 q = 1) (hb : d364822 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361723, d364822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361723, d364822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d361724 q = 1) (hb : d364823 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361724, d364823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361724, d364823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361786 q = 1) (hb : d364830 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361786, d364830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d361786, d364830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100622 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d361793 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d361794 q = 1) (hb : d364831 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361794, d364831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361794, d364831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d361795 q = 1) (hb : d364832 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361795, d364832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361795, d364832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d361796 q = 1) (hb : d364833 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361796, d364833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361796, d364833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d361797 q = 1) (hb : d364834 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361797, d364834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361797, d364834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d361798 q = 1) (hb : d364835 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d361798, d364835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361798, d364835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100624 (p : Pattern) (ha : d361804 p = 1) (hb : d364841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361799 q = 1) (hb : d364836 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d361799, d364836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361799, d364836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100623 q ha hb
  have h2 (q : Pattern) (ha : d361800 q = 1) (hb : d364837 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d361800, d364837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361800, d364837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361801 q = 1) (hb : d364838 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d361801, d364838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361801, d364838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361802 q = 1) (hb : d364839 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d361802, d364839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361802, d364839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361803 q = 1) (hb : d364840 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d361803, d364840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361803, d364840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361804 q = 1) (hb : d364841 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d361804, d364841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361804, d364841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100625 (p : Pattern) (ha : d364471 p = 1) (hb : d364847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361805 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d361561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361805 q = 1) (hb : d364842 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d361805, d364842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361805, d364842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100624 q ha hb
  have h3 (q : Pattern) (ha : d361805 q = 1) (hb : d364843 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d364843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d364843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d364468 q = 1) (hb : d364844 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364468, d364844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364468, d364844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d364469 q = 1) (hb : d364845 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d364469, d364845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364469, d364845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d364470 q = 1) (hb : d364846 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d364470, d364846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d364470, d364846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d364471 q = 1) (hb : d364847 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d364471, d364847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d364471, d364847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro100626 (p : Pattern) (ha : d364477 p = 1) (hb : d364853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364472 q = 1) (hb : d364848 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d364472, d364848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100625 q ha hb
    | true =>
      simp only [d364472, d364848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364473 q = 1) (hb : d364849 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d364473, d364849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364473, d364849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364474 q = 1) (hb : d364850 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d364474, d364850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364474, d364850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364475 q = 1) (hb : d364851 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d364475, d364851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364475, d364851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364476 q = 1) (hb : d364852 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d364476, d364852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364476, d364852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364477 q = 1) (hb : d364853 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d364477, d364853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364477, d364853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100627 (p : Pattern) (ha : d364483 p = 1) (hb : d364859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364478 q = 1) (hb : d364854 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d364478, d364854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100626 q ha hb
    | true =>
      simp only [d364478, d364854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364479 q = 1) (hb : d364855 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d364479, d364855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364479, d364855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364480 q = 1) (hb : d364856 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d364480, d364856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364480, d364856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364481 q = 1) (hb : d364857 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d364481, d364857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364481, d364857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364482 q = 1) (hb : d364858 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d364482, d364858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364482, d364858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364483 q = 1) (hb : d364859 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d364483, d364859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364483, d364859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100628 (p : Pattern) (ha : d364489 p = 1) (hb : d364865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364484 q = 1) (hb : d364860 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d364484, d364860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100627 q ha hb
    | true =>
      simp only [d364484, d364860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364485 q = 1) (hb : d364861 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d364485, d364861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364485, d364861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364486 q = 1) (hb : d364862 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d364486, d364862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364486, d364862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364487 q = 1) (hb : d364863 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d364487, d364863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364487, d364863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364488 q = 1) (hb : d364864 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d364488, d364864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364488, d364864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364489 q = 1) (hb : d364865 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d364489, d364865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364489, d364865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100629 (p : Pattern) (ha : d364495 p = 1) (hb : d364871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364490 q = 1) (hb : d364866 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d364490, d364866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100628 q ha hb
    | true =>
      simp only [d364490, d364866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364491 q = 1) (hb : d364867 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d364491, d364867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364491, d364867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364492 q = 1) (hb : d364868 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d364492, d364868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364492, d364868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364493 q = 1) (hb : d364869 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d364493, d364869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364493, d364869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364494 q = 1) (hb : d364870 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d364494, d364870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364494, d364870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364495 q = 1) (hb : d364871 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d364495, d364871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364495, d364871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100630 (p : Pattern) (ha : d364501 p = 1) (hb : d364877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364496 q = 1) (hb : d364872 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d364496, d364872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100629 q ha hb
    | true =>
      simp only [d364496, d364872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364497 q = 1) (hb : d364873 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d364497, d364873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364497, d364873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364498 q = 1) (hb : d364874 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d364498, d364874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364498, d364874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364499 q = 1) (hb : d364875 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d364499, d364875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364499, d364875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364500 q = 1) (hb : d364876 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d364500, d364876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364500, d364876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364501 q = 1) (hb : d364877 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d364501, d364877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364501, d364877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100631 (p : Pattern) (ha : d364507 p = 1) (hb : d364883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364502 q = 1) (hb : d364878 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d364502, d364878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100630 q ha hb
    | true =>
      simp only [d364502, d364878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364503 q = 1) (hb : d364879 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d364503, d364879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364503, d364879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364504 q = 1) (hb : d364880 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d364504, d364880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364504, d364880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364505 q = 1) (hb : d364881 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d364505, d364881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364505, d364881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364506 q = 1) (hb : d364882 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d364506, d364882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364506, d364882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364507 q = 1) (hb : d364883 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d364507, d364883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364507, d364883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100632 (p : Pattern) (ha : d364513 p = 1) (hb : d364889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364508 q = 1) (hb : d364884 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d364508, d364884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100631 q ha hb
    | true =>
      simp only [d364508, d364884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d364509 q = 1) (hb : d364885 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d364509, d364885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364509, d364885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d364510 q = 1) (hb : d364886 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d364510, d364886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364510, d364886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d364511 q = 1) (hb : d364887 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d364511, d364887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364511, d364887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d364512 q = 1) (hb : d364888 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d364512, d364888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364512, d364888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d364513 q = 1) (hb : d364889 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d364513, d364889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364513, d364889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100633 (p : Pattern) (ha : d363016 p = 1) (hb : d364567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359450 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d359510 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d364562 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363012 q = 1) (hb : d364563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363012, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d363012, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d359562 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d363013 q = 1) (hb : d364564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363013, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d363013, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d363014 q = 1) (hb : d364565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363014, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d363014, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d363015 q = 1) (hb : d364566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363015, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363015, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d363016 q = 1) (hb : d364567 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363016, d364567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363016, d364567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro100634 (p : Pattern) (ha : d363021 p = 1) (hb : d364577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d359450 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359459 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359510 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d364562 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d363012 q = 1) (hb : d364563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363012, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d363012, d364563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d359562 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d363013 q = 1) (hb : d364564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363013, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363013, d364564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d363014 q = 1) (hb : d364565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363014, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363014, d364565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363015 q = 1) (hb : d364566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363015, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363015, d364566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d359572 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d359577 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d359579 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d364572 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d363017 q = 1) (hb : d364573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363017, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d363017, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d359586 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d363018 q = 1) (hb : d364574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363018, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d363018, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d363019 q = 1) (hb : d364575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363019, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d363019, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d363020 q = 1) (hb : d364576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363020, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d363020, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d363021 q = 1) (hb : d364577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363021, d364577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d363021, d364577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro100635 (p : Pattern) (ha : d363028 p = 1) (hb : d364818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359579 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d364572 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363017 q = 1) (hb : d364573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363017, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363017, d364573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d359586 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363018 q = 1) (hb : d364574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363018, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363018, d364574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d363026 q = 1) (hb : d364575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363026, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363026, d364575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363027 q = 1) (hb : d364576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363027, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363027, d364576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363028 q = 1) (hb : d364818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363028, d364818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363028, d364818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100636 (p : Pattern) (ha : d363038 p = 1) (hb : d364829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d359662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d364824 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363034 q = 1) (hb : d364825 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d363034, d364825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363034, d364825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d359702 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363035 q = 1) (hb : d364826 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d363035, d364826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363035, d364826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d363036 q = 1) (hb : d364827 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d363036, d364827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363036, d364827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363037 q = 1) (hb : d364828 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d363037, d364828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363037, d364828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d363038 q = 1) (hb : d364829 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d363038, d364829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363038, d364829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100637 (p : Pattern) (ha : d363044 p = 1) (hb : d364835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d359442 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363022 q = 1) (hb : d364578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363022, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100633 q ha hb
    | true =>
      simp only [d363022, d364578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100634 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d359604 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d363023 q = 1) (hb : d364579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363023, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d363023, d364579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d363024 q = 1) (hb : d364816 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363024, d364816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d363024, d364816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363025 q = 1) (hb : d364817 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363025, d364817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d363025, d364817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d363029 q = 1) (hb : d364819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363029, d364819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363029, d364819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100635 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d359613 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d363030 q = 1) (hb : d364820 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363030, d364820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d363030, d364820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d363031 q = 1) (hb : d364821 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363031, d364821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d363031, d364821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d363032 q = 1) (hb : d364822 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363032, d364822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d363032, d364822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d363033 q = 1) (hb : d364823 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d363033, d364823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d363033, d364823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d363039 q = 1) (hb : d364830 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d363039, d364830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d363039, d364830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100636 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d359718 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d363040 q = 1) (hb : d364831 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d363040, d364831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d363040, d364831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d363041 q = 1) (hb : d364832 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d363041, d364832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d363041, d364832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d363042 q = 1) (hb : d364833 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d363042, d364833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d363042, d364833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d363043 q = 1) (hb : d364834 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d363043, d364834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d363043, d364834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d363044 q = 1) (hb : d364835 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d363044, d364835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d363044, d364835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100638 (p : Pattern) (ha : d363050 p = 1) (hb : d364841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363045 q = 1) (hb : d364836 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d363045, d364836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363045, d364836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100637 q ha hb
  have h2 (q : Pattern) (ha : d363046 q = 1) (hb : d364837 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d363046, d364837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363046, d364837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d363047 q = 1) (hb : d364838 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d363047, d364838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363047, d364838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d363048 q = 1) (hb : d364839 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d363048, d364839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363048, d364839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d363049 q = 1) (hb : d364840 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d363049, d364840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363049, d364840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d363050 q = 1) (hb : d364841 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d363050, d364841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363050, d364841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100639 (p : Pattern) (ha : d364847 p = 1) (hb : d364893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d363011 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d363051 q = 1) (hb : d364842 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d363051, d364842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d363051, d364842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100638 q ha hb
  have h3 (q : Pattern) (ha : d363051 q = 1) (hb : d364843 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d364843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d364843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d364844 q = 1) (hb : d364890 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d364844, d364890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d364844, d364890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d364845 q = 1) (hb : d364891 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d364845, d364891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364845, d364891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d364846 q = 1) (hb : d364892 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d364846, d364892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d364846, d364892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h8 (q : Pattern) (ha : d364847 q = 1) (hb : d364893 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d364847, d364893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d364847, d364893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  exact h8 p ha hb
theorem andIntro100640 (p : Pattern) (ha : d364853 p = 1) (hb : d364899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364848 q = 1) (hb : d364894 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d364848, d364894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100639 q ha hb
    | true =>
      simp only [d364848, d364894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364849 q = 1) (hb : d364895 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d364849, d364895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364849, d364895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364850 q = 1) (hb : d364896 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d364850, d364896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364850, d364896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364851 q = 1) (hb : d364897 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d364851, d364897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364851, d364897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364852 q = 1) (hb : d364898 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d364852, d364898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364852, d364898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364853 q = 1) (hb : d364899 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d364853, d364899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364853, d364899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100641 (p : Pattern) (ha : d364859 p = 1) (hb : d364905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364854 q = 1) (hb : d364900 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d364854, d364900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100640 q ha hb
    | true =>
      simp only [d364854, d364900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364855 q = 1) (hb : d364901 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d364855, d364901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364855, d364901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364856 q = 1) (hb : d364902 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d364856, d364902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364856, d364902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364857 q = 1) (hb : d364903 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d364857, d364903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364857, d364903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364858 q = 1) (hb : d364904 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d364858, d364904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364858, d364904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364859 q = 1) (hb : d364905 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d364859, d364905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364859, d364905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100642 (p : Pattern) (ha : d364865 p = 1) (hb : d364911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364860 q = 1) (hb : d364906 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d364860, d364906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100641 q ha hb
    | true =>
      simp only [d364860, d364906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364861 q = 1) (hb : d364907 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d364861, d364907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364861, d364907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364862 q = 1) (hb : d364908 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d364862, d364908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364862, d364908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364863 q = 1) (hb : d364909 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d364863, d364909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364863, d364909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364864 q = 1) (hb : d364910 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d364864, d364910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364864, d364910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364865 q = 1) (hb : d364911 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d364865, d364911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364865, d364911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100643 (p : Pattern) (ha : d364871 p = 1) (hb : d364917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364866 q = 1) (hb : d364912 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d364866, d364912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100642 q ha hb
    | true =>
      simp only [d364866, d364912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364867 q = 1) (hb : d364913 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d364867, d364913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364867, d364913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364868 q = 1) (hb : d364914 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d364868, d364914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364868, d364914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364869 q = 1) (hb : d364915 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d364869, d364915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364869, d364915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364870 q = 1) (hb : d364916 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d364870, d364916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364870, d364916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364871 q = 1) (hb : d364917 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d364871, d364917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364871, d364917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100644 (p : Pattern) (ha : d364877 p = 1) (hb : d364923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364872 q = 1) (hb : d364918 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d364872, d364918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100643 q ha hb
    | true =>
      simp only [d364872, d364918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364873 q = 1) (hb : d364919 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d364873, d364919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364873, d364919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364874 q = 1) (hb : d364920 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d364874, d364920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364874, d364920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364875 q = 1) (hb : d364921 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d364875, d364921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364875, d364921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364876 q = 1) (hb : d364922 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d364876, d364922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364876, d364922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364877 q = 1) (hb : d364923 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d364877, d364923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364877, d364923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100645 (p : Pattern) (ha : d364883 p = 1) (hb : d364929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364878 q = 1) (hb : d364924 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d364878, d364924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100644 q ha hb
    | true =>
      simp only [d364878, d364924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364879 q = 1) (hb : d364925 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d364879, d364925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364879, d364925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364880 q = 1) (hb : d364926 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d364880, d364926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364880, d364926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364881 q = 1) (hb : d364927 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d364881, d364927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364881, d364927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364882 q = 1) (hb : d364928 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d364882, d364928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364882, d364928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364883 q = 1) (hb : d364929 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d364883, d364929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364883, d364929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100646 (p : Pattern) (ha : d364889 p = 1) (hb : d364935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d364884 q = 1) (hb : d364930 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d364884, d364930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100645 q ha hb
    | true =>
      simp only [d364884, d364930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d364885 q = 1) (hb : d364931 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d364885, d364931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d364885, d364931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d364886 q = 1) (hb : d364932 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d364886, d364932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d364886, d364932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d364887 q = 1) (hb : d364933 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d364887, d364933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d364887, d364933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d364888 q = 1) (hb : d364934 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d364888, d364934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d364888, d364934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d364889 q = 1) (hb : d364935 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d364889, d364935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d364889, d364935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100647 (p : Pattern) (ha : d24 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d24 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d24, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100648 (p : Pattern) (ha : d30 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d28 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d29 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100649 (p : Pattern) (ha : d308 p = 1) (hb : d42255 p = 1) : d364527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42253 q = 1) : d364514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42253, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42254 q = 1) : d364515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42254, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42255 q = 1) : d364527 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42255, d364527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42255, d364527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro100650 (p : Pattern) (ha : d308 p = 1) (hb : d42261 p = 1) : d364540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42256 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100649 q ha hb
    | true =>
      simp only [d42256, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42257 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42257, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42258 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42258, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42258, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42259 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42259, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42259, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42260 q = 1) : d364535 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42260, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42260, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42261 q = 1) : d364540 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42261, d364540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42261, d364540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro100651 (p : Pattern) (ha : d308 p = 1) (hb : d42377 p = 1) : d364527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42250 q = 1) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100300 q ha hb
    | true =>
      simp only [d42250, d1564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42251 q = 1) : d1565 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d1565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42252 q = 1) : d1578 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42375 q = 1) : d364514 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42375, d364514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42376 q = 1) : d364515 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42376, d364515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d21 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d23, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42377 q = 1) : d364527 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42377, d364527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42377, d364527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro100652 (p : Pattern) (ha : d308 p = 1) (hb : d42383 p = 1) : d364536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42370 q = 1) : d364517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100489 q ha hb
    | true =>
      simp only [d42370, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42371 q = 1) : d364518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42371, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42372 q = 1) : d364519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42372, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42372, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42373 q = 1) : d364520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42373, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42373, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42256 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100649 q ha hb
    | true =>
      simp only [d42256, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42257 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42257, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42258 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42258, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42258, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42259 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42259, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42259, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42374 q = 1) : d364534 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42374, d364534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42374, d364534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42378 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
    | true =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42379 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42380 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42380, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42381 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42381, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d25 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d27 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d28 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42382 q = 1) : d364535 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42382, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42382, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42383 q = 1) : d364536 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42383, d364536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42383, d364536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100653 (p : Pattern) (ha : d308 p = 1) (hb : d42540 p = 1) : d365066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42384 q = 1) : d364541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100652 q ha hb
    | true =>
      simp only [d42384, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100650 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42385 q = 1) : d364542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42385, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42386 q = 1) : d364543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42386, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42262 q = 1) : d365060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100650 q ha hb
    | true =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100648 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42263 q = 1) : d365061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42264 q = 1) : d365062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42387 q = 1) : d365063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42387, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42538 q = 1) : d365064 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42538, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42538, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42539 q = 1) : d365065 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42539, d365065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42539, d365065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42540 q = 1) : d365066 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42540, d365066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42540, d365066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100654 (p : Pattern) (ha : d308 p = 1) (hb : d42544 p = 1) : d365070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42262 q = 1) : d365060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100650 q ha hb
    | true =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100648 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42263 q = 1) : d365061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42264 q = 1) : d365062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42538 q = 1) : d365064 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42538, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42538, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42543 q = 1) : d365069 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42543, d365069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42543, d365069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42544 q = 1) : d365070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42544, d365070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42544, d365070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100655 (p : Pattern) (ha : d308 p = 1) (hb : d42550 p = 1) : d365076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42547 q = 1) : d365073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42548 q = 1) : d365074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42549 q = 1) : d365075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42549, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42549, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42550 q = 1) : d365076 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42550, d365076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42550, d365076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100656 (p : Pattern) (ha : d308 p = 1) (hb : d42554 p = 1) : d365080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42551 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42552 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42553 q = 1) : d365079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42553, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42553, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42554 q = 1) : d365080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42554, d365080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42554, d365080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100657 (p : Pattern) (ha : d308 p = 1) (hb : d42560 p = 1) : d365086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42555 q = 1) : d365081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100655 q ha hb
    | true =>
      simp only [d42555, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100656 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42556 q = 1) : d365082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42556, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42557 q = 1) : d365083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42558 q = 1) : d365084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42558, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42559 q = 1) : d365085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42559, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42560 q = 1) : d365086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42560, d365086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42560, d365086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100658 (p : Pattern) (ha : d308 p = 1) (hb : d42563 p = 1) : d365089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42547 q = 1) : d365073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42548 q = 1) : d365074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42549 q = 1) : d365075 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42549, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42549, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42563 q = 1) : d365089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42563, d365089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42563, d365089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100659 (p : Pattern) (ha : d308 p = 1) (hb : d42564 p = 1) : d365090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42551 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42552 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42553 q = 1) : d365079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42553, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42553, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42564 q = 1) : d365090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42564, d365090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42564, d365090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100660 (p : Pattern) (ha : d308 p = 1) (hb : d42570 p = 1) : d365096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42555 q = 1) : d365081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100655 q ha hb
    | true =>
      simp only [d42555, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100656 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42556 q = 1) : d365082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42556, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42557 q = 1) : d365083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42558 q = 1) : d365084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42558, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42559 q = 1) : d365085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42559, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42565 q = 1) : d365091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42565, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100658 q ha hb
    | true =>
      simp only [d42565, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100659 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42566 q = 1) : d365092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42566, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42566, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42567 q = 1) : d365093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42567, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42567, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42568 q = 1) : d365094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42568, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42568, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42569 q = 1) : d365095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42569, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42569, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42570 q = 1) : d365096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42570, d365096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42570, d365096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100661 (p : Pattern) (ha : d308 p = 1) (hb : d42730 p = 1) : d365164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42555 q = 1) : d365081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100655 q ha hb
    | true =>
      simp only [d42555, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100656 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42556 q = 1) : d365082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42556, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42557 q = 1) : d365083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42558 q = 1) : d365084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42558, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42559 q = 1) : d365085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42559, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42725 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42725, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100656 q ha hb
    | true =>
      simp only [d42725, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42726 q = 1) : d365160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42726, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42726, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42727 q = 1) : d365161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42727, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42727, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42728 q = 1) : d365162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42728, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42728, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42729 q = 1) : d365163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42729, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42729, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42730 q = 1) : d365164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42730, d365164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42730, d365164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100662 (p : Pattern) (ha : d308 p = 1) (hb : d42736 p = 1) : d365170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42725 q = 1) : d365159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42725, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100656 q ha hb
    | true =>
      simp only [d42725, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42726 q = 1) : d365160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42726, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42726, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42727 q = 1) : d365161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42727, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42727, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42728 q = 1) : d365162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42728, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42728, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42729 q = 1) : d365163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42729, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42729, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42731 q = 1) : d365165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42731, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100659 q ha hb
    | true =>
      simp only [d42731, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42732 q = 1) : d365166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42732, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42732, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42733 q = 1) : d365167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42733, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42733, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42734 q = 1) : d365168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42734, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42734, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42735 q = 1) : d365169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42735, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42735, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42736 q = 1) : d365170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42736, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42736, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100663 (p : Pattern) (ha : d308 p = 1) (hb : d42745 p = 1) : d365179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42731 q = 1) : d365165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42731, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100659 q ha hb
    | true =>
      simp only [d42731, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42732 q = 1) : d365166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42732, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42732, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42733 q = 1) : d365167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42733, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42733, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42734 q = 1) : d365168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42734, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42734, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42735 q = 1) : d365169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42735, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42735, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42745 q = 1) : d365179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42745, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42745, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100664 (p : Pattern) (ha : d71 p = 1) (hb : d308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d66 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d67 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d68 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d70 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d71 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d71, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro100665 (p : Pattern) (ha : d308 p = 1) (hb : d42304 p = 1) : d364707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42299 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42299, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42299, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100649 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42256 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100649 q ha hb
    | true =>
      simp only [d42256, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42300 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42300, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42300, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42257 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42257, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42301 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42301, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42301, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42302 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42302, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42302, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42303 q = 1) : d364696 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42303, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42303, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42304 q = 1) : d364707 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42304, d364707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42304, d364707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro100666 (p : Pattern) (ha : d308 p = 1) (hb : d42788 p = 1) : d365203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42305 q = 1) : d365185 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100665 q ha hb
    | true =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100664 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42306 q = 1) : d365186 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42307 q = 1) : d365187 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42778 q = 1) : d365193 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42778, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42778, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42787 q = 1) : d365202 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42787, d365202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42787, d365202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42788 q = 1) : d365203 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42788, d365203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42788, d365203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100667 (p : Pattern) (ha : d308 p = 1) (hb : d42844 p = 1) : d365226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42789 q = 1) : d365204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42789, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100666 q ha hb
    | true =>
      simp only [d42789, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42790 q = 1) : d365205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42790, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42790, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42841 q = 1) : d365223 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42841, d365223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42841, d365223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42842 q = 1) : d365224 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42842, d365224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42842, d365224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42843 q = 1) : d365225 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42843, d365225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42843, d365225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42844 q = 1) : d365226 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42844, d365226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42844, d365226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100668 (p : Pattern) (ha : d308 p = 1) (hb : d42850 p = 1) : d365232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42845 q = 1) : d365227 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42845, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100667 q ha hb
    | true =>
      simp only [d42845, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42846 q = 1) : d365228 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42846, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42846, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42847 q = 1) : d365229 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42847, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42847, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42848 q = 1) : d365230 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42848, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42848, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42849 q = 1) : d365231 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42849, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42849, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42850 q = 1) : d365232 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42850, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42850, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100669 (p : Pattern) (ha : d308 p = 1) (hb : d42575 p = 1) : d365101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42547 q = 1) : d365073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42548 q = 1) : d365074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42574 q = 1) : d365100 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42574, d365100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42574, d365100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42575 q = 1) : d365101 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42575, d365101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42575, d365101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100670 (p : Pattern) (ha : d308 p = 1) (hb : d42577 p = 1) : d365103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42551 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42552 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42576 q = 1) : d365102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42576, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42576, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42577 q = 1) : d365103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42577, d365103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42577, d365103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100671 (p : Pattern) (ha : d308 p = 1) (hb : d42584 p = 1) : d365110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42547 q = 1) : d365073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42582 q = 1) : d365108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42582, d365108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42582, d365108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42583 q = 1) : d365109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42583, d365109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42583, d365109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42584 q = 1) : d365110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42584, d365110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42584, d365110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100672 (p : Pattern) (ha : d308 p = 1) (hb : d42587 p = 1) : d365113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42551 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42585 q = 1) : d365111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42585, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42585, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42586 q = 1) : d365112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42586, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42586, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42587 q = 1) : d365113 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42587, d365113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42587, d365113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100673 (p : Pattern) (ha : d308 p = 1) (hb : d42626 p = 1) : d364533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42608 q = 1) : d363948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100484 q ha hb
    | true =>
      simp only [d42608, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42609 q = 1) : d363949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42609, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42610 q = 1) : d363950 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42610, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42610, d363950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42611 q = 1) : d363951 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42611, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42611, d363951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42613 q = 1) : d364517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100485 q ha hb
    | true =>
      simp only [d42613, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42614 q = 1) : d364518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42614, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42615 q = 1) : d364519 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42615, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42615, d364519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42616 q = 1) : d364520 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42616, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42616, d364520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42617 q = 1) : d364521 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42617, d364521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42617, d364521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42621 q = 1) : d364523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
    | true =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42622 q = 1) : d364524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42623 q = 1) : d364525 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42623, d364525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42624 q = 1) : d364526 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42624, d364526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42378 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
    | true =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42379 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42380 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42380, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42381 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42381, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42625 q = 1) : d364532 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42625, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42625, d364532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42626 q = 1) : d364533 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42626, d364533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42626, d364533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro100674 (p : Pattern) (ha : d308 p = 1) (hb : d42630 p = 1) : d364540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42378 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
    | true =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42379 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42380 q = 1) : d364530 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42380, d364530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42381 q = 1) : d364531 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42381, d364531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d25 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d28 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42382 q = 1) : d364535 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42382, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42382, d364535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d29 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42630 q = 1) : d364540 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42630, d364540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42630, d364540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro100675 (p : Pattern) (ha : d308 p = 1) (hb : d42636 p = 1) : d365118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42627 q = 1) : d364537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42627, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100673 q ha hb
    | true =>
      simp only [d42627, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100652 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42628 q = 1) : d364538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42628, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42628, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42629 q = 1) : d364539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42629, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42629, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42631 q = 1) : d364541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42631, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100652 q ha hb
    | true =>
      simp only [d42631, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100674 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42632 q = 1) : d364542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42632, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42632, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42633 q = 1) : d364543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42633, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42633, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42634 q = 1) : d364544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42634, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42634, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42384 q = 1) : d364541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100652 q ha hb
    | true =>
      simp only [d42384, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100650 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42385 q = 1) : d364542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42385, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42386 q = 1) : d364543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42386, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42262 q = 1) : d365060 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100650 q ha hb
    | true =>
      simp only [d42262, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100648 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42263 q = 1) : d365061 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42263, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42264 q = 1) : d365062 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42264, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42387 q = 1) : d365063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42387, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42635 q = 1) : d365117 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42635, d365117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42635, d365117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42636 q = 1) : d365118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42636, d365118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42636, d365118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100676 (p : Pattern) (ha : d308 p = 1) (hb : d42642 p = 1) : d365124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42637 q = 1) : d365119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42637, d365119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100675 q ha hb
    | true =>
      simp only [d42637, d365119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42638 q = 1) : d365120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42638, d365120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42638, d365120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42639 q = 1) : d365121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42639, d365121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42639, d365121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42640 q = 1) : d365122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42640, d365122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42640, d365122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42641 q = 1) : d365123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42641, d365123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42641, d365123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42642 q = 1) : d365124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42642, d365124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42642, d365124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100677 (p : Pattern) (ha : d308 p = 1) (hb : d42693 p = 1) : d365130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42690 q = 1) : d365127 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42690, d365127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42690, d365127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42691 q = 1) : d365128 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42691, d365128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42691, d365128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42692 q = 1) : d365129 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42692, d365129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42692, d365129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42693 q = 1) : d365130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42693, d365130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42693, d365130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100678 (p : Pattern) (ha : d308 p = 1) (hb : d309848 p = 1) : d365136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42578 q = 1) : d365104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42578, d365104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100669 q ha hb
    | true =>
      simp only [d42578, d365104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100670 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42579 q = 1) : d365105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42579, d365105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42579, d365105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42580 q = 1) : d365106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42580, d365106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42580, d365106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42581 q = 1) : d365107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42581, d365107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42581, d365107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42588 q = 1) : d365114 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42588, d365114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100671 q ha hb
    | true =>
      simp only [d42588, d365114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100672 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42589 q = 1) : d365115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42589, d365115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42589, d365115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42590 q = 1) : d365116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42590, d365116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42590, d365116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42643 q = 1) : d365125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42643, d365125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100676 q ha hb
    | true =>
      simp only [d42643, d365125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100655 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309844 q = 1) : d365126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d365126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309844, d365126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42694 q = 1) : d365131 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42694, d365131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100677 q ha hb
    | true =>
      simp only [d42694, d365131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42695 q = 1) : d365132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42695, d365132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42695, d365132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309845 q = 1) : d365133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d365133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309845, d365133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309846 q = 1) : d365134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d365134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309846, d365134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309847 q = 1) : d365135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d365135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309847, d365135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309848 q = 1) : d365136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309848, d365136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309848, d365136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro100679 (p : Pattern) (ha : d308 p = 1) (hb : d42700 p = 1) : d365137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42547 q = 1) : d365073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42548 q = 1) : d365074 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42574 q = 1) : d365100 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42574, d365100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42574, d365100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42700 q = 1) : d365137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42700, d365137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42700, d365137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100680 (p : Pattern) (ha : d308 p = 1) (hb : d42701 p = 1) : d365138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42551 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42552 q = 1) : d365078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42576 q = 1) : d365102 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42576, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42576, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42701 q = 1) : d365138 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42701, d365138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42701, d365138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100681 (p : Pattern) (ha : d308 p = 1) (hb : d42706 p = 1) : d365143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42547 q = 1) : d365073 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42582 q = 1) : d365108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42582, d365108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42582, d365108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42583 q = 1) : d365109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42583, d365109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42583, d365109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42706 q = 1) : d365143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42706, d365143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42706, d365143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100682 (p : Pattern) (ha : d308 p = 1) (hb : d42707 p = 1) : d365144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42545 q = 1) : d365071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100654 q ha hb
    | true =>
      simp only [d42545, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42546 q = 1) : d365072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42546, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42551 q = 1) : d365077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42585 q = 1) : d365111 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42585, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42585, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42586 q = 1) : d365112 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42586, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42586, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42707 q = 1) : d365144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42707, d365144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42707, d365144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100683 (p : Pattern) (ha : d308 p = 1) (hb : d42711 p = 1) : d365148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42637 q = 1) : d365119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42637, d365119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100675 q ha hb
    | true =>
      simp only [d42637, d365119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42638 q = 1) : d365120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42638, d365120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42638, d365120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42639 q = 1) : d365121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42639, d365121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42639, d365121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42640 q = 1) : d365122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42640, d365122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42640, d365122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42641 q = 1) : d365123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42641, d365123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42641, d365123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42711 q = 1) : d365148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42711, d365148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42711, d365148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100684 (p : Pattern) (ha : d308 p = 1) (hb : d42717 p = 1) : d365151 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42541 q = 1) : d365067 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100653 q ha hb
    | true =>
      simp only [d42541, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42542 q = 1) : d365068 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42542, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42690 q = 1) : d365127 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42690, d365127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42690, d365127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42691 q = 1) : d365128 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42691, d365128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42691, d365128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42692 q = 1) : d365129 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42692, d365129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42692, d365129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42717 q = 1) : d365151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42717, d365151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42717, d365151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100685 (p : Pattern) (ha : d308 p = 1) (hb : d309853 p = 1) : d365157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42578 q = 1) : d365104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42578, d365104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100669 q ha hb
    | true =>
      simp only [d42578, d365104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100670 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42579 q = 1) : d365105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42579, d365105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42579, d365105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42580 q = 1) : d365106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42580, d365106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42580, d365106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42581 q = 1) : d365107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42581, d365107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42581, d365107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42588 q = 1) : d365114 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42588, d365114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100671 q ha hb
    | true =>
      simp only [d42588, d365114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100672 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42589 q = 1) : d365115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42589, d365115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42589, d365115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42590 q = 1) : d365116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42590, d365116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42590, d365116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42643 q = 1) : d365125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42643, d365125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100676 q ha hb
    | true =>
      simp only [d42643, d365125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100655 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309844 q = 1) : d365126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d365126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309844, d365126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42694 q = 1) : d365131 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42694, d365131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100677 q ha hb
    | true =>
      simp only [d42694, d365131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42695 q = 1) : d365132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42695, d365132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42695, d365132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d309845 q = 1) : d365133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d365133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309845, d365133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309846 q = 1) : d365134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d365134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309846, d365134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309847 q = 1) : d365135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d365135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d309847, d365135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42702 q = 1) : d365139 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42702, d365139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100679 q ha hb
    | true =>
      simp only [d42702, d365139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100680 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42703 q = 1) : d365140 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42703, d365140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42703, d365140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42704 q = 1) : d365141 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42704, d365141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42704, d365141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42705 q = 1) : d365142 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42705, d365142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42705, d365142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42708 q = 1) : d365145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42708, d365145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100681 q ha hb
    | true =>
      simp only [d42708, d365145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100682 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d42709 q = 1) : d365146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42709, d365146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42709, d365146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d42710 q = 1) : d365147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42710, d365147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42710, d365147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d42712 q = 1) : d365149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42712, d365149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100683 q ha hb
    | true =>
      simp only [d42712, d365149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100658 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309849 q = 1) : d365150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d365150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309849, d365150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d42718 q = 1) : d365152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42718, d365152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100684 q ha hb
    | true =>
      simp only [d42718, d365152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d42719 q = 1) : d365153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42719, d365153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42719, d365153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d309850 q = 1) : d365154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d365154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309850, d365154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d309851 q = 1) : d365155 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309851, d365155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309851, d365155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d308 q = 1) (hb : d309852 q = 1) : d365156 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309852, d365156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309852, d365156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d308 q = 1) (hb : d309853 q = 1) : d365157 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309853, d365157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309853, d365157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro100686 (p : Pattern) (ha : d308 p = 1) (hb : d309860 p = 1) : d365177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42712 q = 1) : d365149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42712, d365149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100683 q ha hb
    | true =>
      simp only [d42712, d365149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100658 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309849 q = 1) : d365150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d365150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309849, d365150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42718 q = 1) : d365152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42718, d365152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100684 q ha hb
    | true =>
      simp only [d42718, d365152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42719 q = 1) : d365153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42719, d365153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42719, d365153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309850 q = 1) : d365154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d365154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309850, d365154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309858 q = 1) : d365175 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309858, d365175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309858, d365175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309859 q = 1) : d365176 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309859, d365176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309859, d365176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309860 q = 1) : d365177 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309860, d365177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309860, d365177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100687 (p : Pattern) (ha : d308 p = 1) (hb : d42482 p = 1) : d364703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42472 q = 1) : d364682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42472, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42472, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100489 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42370 q = 1) : d364517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100489 q ha hb
    | true =>
      simp only [d42370, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42473 q = 1) : d364683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42473, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42473, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42371 q = 1) : d364518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42371, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42474 q = 1) : d364684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42474, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42474, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42475 q = 1) : d364685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42475, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42475, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42299 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42299, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42299, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100649 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42256 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100649 q ha hb
    | true =>
      simp only [d42256, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42300 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42300, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42300, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42257 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42257, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42301 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42301, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42301, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42302 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42302, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42302, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42476 q = 1) : d364702 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42476, d364702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42476, d364702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42477 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42477, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42378 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
    | true =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42478 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42478, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42379 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42479 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42479, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42480 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42480, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
  have h21 (q : Pattern) (ha : d25 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d67 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d26 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d68 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d69 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d42481 q = 1) : d364696 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42481, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42481, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d42482 q = 1) : d364703 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42482, d364703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42482, d364703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100688 (p : Pattern) (ha : d308 p = 1) (hb : d42765 p = 1) : d364692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42751 q = 1) : d364160 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42751, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42751, d364160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100484 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42608 q = 1) : d363948 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100484 q ha hb
    | true =>
      simp only [d42608, d363948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42752 q = 1) : d364161 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42752, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42752, d364161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42609 q = 1) : d363949 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42609, d363949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42753 q = 1) : d364162 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42753, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42753, d364162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42754 q = 1) : d364163 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42754, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42754, d364163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42755 q = 1) : d364682 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42755, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42755, d364682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100485 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42613 q = 1) : d364517 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100485 q ha hb
    | true =>
      simp only [d42613, d364517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42756 q = 1) : d364683 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42756, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42756, d364683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42614 q = 1) : d364518 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42614, d364518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42757 q = 1) : d364684 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42757, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42757, d364684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42758 q = 1) : d364685 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42758, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42758, d364685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42759 q = 1) : d364686 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42759, d364686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42759, d364686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42760 q = 1) : d364676 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42760, d364676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42621 q = 1) : d364523 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100486 q ha hb
    | true =>
      simp only [d42621, d364523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42761 q = 1) : d364677 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42761, d364677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d42622 q = 1) : d364524 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42622, d364524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42762 q = 1) : d364678 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42762, d364678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d42763 q = 1) : d364679 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42763, d364679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d42477 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42477, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d42378 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
    | true =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d42478 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42478, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d42379 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d42479 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d42479, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d42480 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42480, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d42764 q = 1) : d364691 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42764, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42764, d364691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d42765 q = 1) : d364692 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42765, d364692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42765, d364692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro100689 (p : Pattern) (ha : d308 p = 1) (hb : d42769 p = 1) : d364707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42477 q = 1) : d364687 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42477, d364687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42378 q = 1) : d364528 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100651 q ha hb
    | true =>
      simp only [d42378, d364528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42478 q = 1) : d364688 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42478, d364688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42379 q = 1) : d364529 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42379, d364529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42479 q = 1) : d364689 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42479, d364689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42480 q = 1) : d364690 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42480, d364690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d66 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
  have h8 (q : Pattern) (ha : d25 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100647 q ha hb
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d67 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d68 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d69 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d69, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42481 q = 1) : d364696 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42481, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42481, d364696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d70 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42769 q = 1) : d364707 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42769, d364707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42769, d364707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro100690 (p : Pattern) (ha : d308 p = 1) (hb : d42775 p = 1) : d365190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42766 q = 1) : d364704 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42766, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100688 q ha hb
    | true =>
      simp only [d42766, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100687 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42767 q = 1) : d364705 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42767, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42767, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42768 q = 1) : d364706 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42768, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42768, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42770 q = 1) : d364708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42770, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100687 q ha hb
    | true =>
      simp only [d42770, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100689 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42771 q = 1) : d364709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42771, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42771, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42772 q = 1) : d364710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42772, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42772, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42773 q = 1) : d364711 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42773, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42773, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42483 q = 1) : d364708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100687 q ha hb
    | true =>
      simp only [d42483, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100665 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42484 q = 1) : d364709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42484, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42485 q = 1) : d364710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42485, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d42305 q = 1) : d365185 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100665 q ha hb
    | true =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100664 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42306 q = 1) : d365186 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d42307 q = 1) : d365187 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d42486 q = 1) : d365188 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42486, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d42774 q = 1) : d365189 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42774, d365189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42774, d365189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d42775 q = 1) : d365190 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42775, d365190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42775, d365190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro100691 (p : Pattern) (ha : d308 p = 1) (hb : d42780 p = 1) : d365195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42483 q = 1) : d364708 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100687 q ha hb
    | true =>
      simp only [d42483, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100665 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42484 q = 1) : d364709 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42484, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42485 q = 1) : d364710 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42485, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42305 q = 1) : d365185 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100665 q ha hb
    | true =>
      simp only [d42305, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100664 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42306 q = 1) : d365186 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42306, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42307 q = 1) : d365187 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42307, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42486 q = 1) : d365188 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42486, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42778 q = 1) : d365193 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42778, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42778, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d42779 q = 1) : d365194 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42779, d365194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42779, d365194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d42780 q = 1) : d365195 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42780, d365195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42780, d365195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100692 (p : Pattern) (ha : d308 p = 1) (hb : d42786 p = 1) : d365201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42776 q = 1) : d365191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42776, d365191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100690 q ha hb
    | true =>
      simp only [d42776, d365191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42777 q = 1) : d365192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42777, d365192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42777, d365192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42781 q = 1) : d365196 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100691 q ha hb
    | true =>
      simp only [d42781, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42782 q = 1) : d365197 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42782, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42783 q = 1) : d365198 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42783, d365198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42783, d365198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42784 q = 1) : d365199 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42784, d365199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42784, d365199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42785 q = 1) : d365200 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42785, d365200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42785, d365200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42786 q = 1) : d365201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42786, d365201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42786, d365201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100693 (p : Pattern) (ha : d308 p = 1) (hb : d42794 p = 1) : d365209 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42781 q = 1) : d365196 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100691 q ha hb
    | true =>
      simp only [d42781, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42782 q = 1) : d365197 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42782, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42789 q = 1) : d365204 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42789, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100666 q ha hb
    | true =>
      simp only [d42789, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42790 q = 1) : d365205 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42790, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42790, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42791 q = 1) : d365206 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42791, d365206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42791, d365206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42792 q = 1) : d365207 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42792, d365207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42792, d365207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42793 q = 1) : d365208 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42793, d365208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42793, d365208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d42794 q = 1) : d365209 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42794, d365209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42794, d365209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100694 (p : Pattern) (ha : d308 p = 1) (hb : d42833 p = 1) : d365215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42781 q = 1) : d365196 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100691 q ha hb
    | true =>
      simp only [d42781, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42782 q = 1) : d365197 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42782, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42830 q = 1) : d365212 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42830, d365212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42830, d365212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42831 q = 1) : d365213 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42831, d365213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42831, d365213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42832 q = 1) : d365214 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42832, d365214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42832, d365214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d42833 q = 1) : d365215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42833, d365215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42833, d365215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100695 (p : Pattern) (ha : d308 p = 1) (hb : d309870 p = 1) : d365221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42795 q = 1) : d365210 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42795, d365210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100692 q ha hb
    | true =>
      simp only [d42795, d365210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100693 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309866 q = 1) : d365211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309866, d365211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309866, d365211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42834 q = 1) : d365216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42834, d365216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100694 q ha hb
    | true =>
      simp only [d42834, d365216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42835 q = 1) : d365217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42835, d365217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42835, d365217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309867 q = 1) : d365218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309867, d365218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309867, d365218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309868 q = 1) : d365219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309868, d365219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309868, d365219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d309869 q = 1) : d365220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309869, d365220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309869, d365220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309870 q = 1) : d365221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309870, d365221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309870, d365221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100696 (p : Pattern) (ha : d308 p = 1) (hb : d309876 p = 1) : d365238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d42561 q = 1) : d365087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42561, d365087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42561, d365087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100657 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d42562 q = 1) : d365088 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42562, d365088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42562, d365088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d42571 q = 1) : d365097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42571, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100657 q ha hb
    | true =>
      simp only [d42571, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100660 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d42572 q = 1) : d365098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42572, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42572, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d42573 q = 1) : d365099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42573, d365099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42573, d365099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309854 q = 1) : d365158 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309854, d365158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100678 q ha hb
    | true =>
      simp only [d309854, d365158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100685 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d42737 q = 1) : d365171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42737, d365171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100661 q ha hb
    | true =>
      simp only [d42737, d365171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100662 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d309855 q = 1) : d365172 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309855, d365172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309855, d365172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d309856 q = 1) : d365173 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309856, d365173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309856, d365173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d309857 q = 1) : d365174 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309857, d365174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309857, d365174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d309861 q = 1) : d365178 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309861, d365178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309861, d365178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100686 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d42746 q = 1) : d365180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42746, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42746, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100663 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d309862 q = 1) : d365181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309862, d365181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309862, d365181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d309863 q = 1) : d365182 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309863, d365182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309863, d365182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d309864 q = 1) : d365183 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309864, d365183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309864, d365183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d309865 q = 1) : d365184 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309865, d365184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309865, d365184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d309871 q = 1) : d365222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309871, d365222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309871, d365222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100695 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d42851 q = 1) : d365233 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42851, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d42851, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100668 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d309872 q = 1) : d365234 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309872, d365234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309872, d365234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d309873 q = 1) : d365235 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309873, d365235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309873, d365235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d309874 q = 1) : d365236 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309874, d365236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309874, d365236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d309875 q = 1) : d365237 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309875, d365237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309875, d365237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d309876 q = 1) : d365238 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309876, d365238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309876, d365238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100697 (p : Pattern) (ha : d308 p = 1) (hb : d309882 p = 1) : d365244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d309877 q = 1) : d365239 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309877, d365239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309877, d365239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100696 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d309878 q = 1) : d365240 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309878, d365240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309878, d365240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d309879 q = 1) : d365241 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309879, d365241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309879, d365241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d309880 q = 1) : d365242 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309880, d365242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309880, d365242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d309881 q = 1) : d365243 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309881, d365243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309881, d365243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d309882 q = 1) : d365244 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309882, d365244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309882, d365244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100698 (p : Pattern) (ha : d310011 p = 1) (hb : d364959 p = 1) : d365250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d309843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d309883 q = 1) (hb : d364955 q = 1) : d365245 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d309883, d364955, d365245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309883, d364955, d365245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100697 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d309923 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d309924 q = 1) (hb : d364956 q = 1) : d365246 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d309924, d364956, d365246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309924, d364956, d365246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309965 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d309966 q = 1) (hb : d364957 q = 1) : d365247 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d309966, d364957, d365247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309966, d364957, d365247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310008 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310009 q = 1) (hb : d364958 q = 1) : d365248 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d310009, d364958, d365248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310009, d364958, d365248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309509 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d310010 q = 1) (hb : d364959 q = 1) : d365249 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d310010, d364959, d365249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d310010, d364959, d365249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d364959 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d310011 q = 1) (hb : d364959 q = 1) : d365250 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d310011, d365250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d310011, d365250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100699 (p : Pattern) (ha : d310017 p = 1) (hb : d364960 p = 1) : d365256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310012 q = 1) (hb : d364959 q = 1) : d365251 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d310012, d365251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100698 q ha hb
    | true =>
      simp only [d310012, d365251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310013 q = 1) (hb : d364959 q = 1) : d365252 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d310013, d365252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310013, d365252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310014 q = 1) (hb : d364959 q = 1) : d365253 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d310014, d365253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310014, d365253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310015 q = 1) (hb : d364959 q = 1) : d365254 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d310015, d365254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310015, d365254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310016 q = 1) (hb : d364959 q = 1) : d365255 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d310016, d365255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310016, d365255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310017 q = 1) (hb : d364960 q = 1) : d365256 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d310017, d364960, d365256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310017, d364960, d365256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100700 (p : Pattern) (ha : d310023 p = 1) (hb : d364965 p = 1) : d365262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310018 q = 1) (hb : d364961 q = 1) : d365257 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d310018, d364961, d365257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100699 q ha hb
    | true =>
      simp only [d310018, d364961, d365257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310019 q = 1) (hb : d364962 q = 1) : d365258 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d310019, d364962, d365258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310019, d364962, d365258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310020 q = 1) (hb : d364963 q = 1) : d365259 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d310020, d364963, d365259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310020, d364963, d365259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310021 q = 1) (hb : d364964 q = 1) : d365260 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d310021, d364964, d365260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310021, d364964, d365260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310022 q = 1) (hb : d364965 q = 1) : d365261 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d310022, d364965, d365261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310022, d364965, d365261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310023 q = 1) (hb : d364965 q = 1) : d365262 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d310023, d365262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310023, d365262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100701 (p : Pattern) (ha : d310029 p = 1) (hb : d364965 p = 1) : d365268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310024 q = 1) (hb : d364965 q = 1) : d365263 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d310024, d365263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100700 q ha hb
    | true =>
      simp only [d310024, d365263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310025 q = 1) (hb : d364965 q = 1) : d365264 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d310025, d365264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310025, d365264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310026 q = 1) (hb : d364965 q = 1) : d365265 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d310026, d365265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310026, d365265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310027 q = 1) (hb : d364965 q = 1) : d365266 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d310027, d365266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310027, d365266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310028 q = 1) (hb : d364965 q = 1) : d365267 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d310028, d365267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310028, d365267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310029 q = 1) (hb : d364965 q = 1) : d365268 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d310029, d365268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310029, d365268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100702 (p : Pattern) (ha : d310035 p = 1) (hb : d364965 p = 1) : d365274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d364965 q = 1) : d365269 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, d365269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100701 q ha hb
    | true =>
      simp only [d310030, d365269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d364965 q = 1) : d365270 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, d365270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, d365270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d364965 q = 1) : d365271 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, d365271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, d365271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d364965 q = 1) : d365272 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, d365272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, d365272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d364965 q = 1) : d365273 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, d365273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, d365273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d364965 q = 1) : d365274 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, d365274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, d365274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100703 (p : Pattern) (ha : d310041 p = 1) (hb : d364965 p = 1) : d365280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d364965 q = 1) : d365275 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, d365275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100702 q ha hb
    | true =>
      simp only [d310036, d365275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d364965 q = 1) : d365276 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, d365276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, d365276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d364965 q = 1) : d365277 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, d365277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, d365277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d364965 q = 1) : d365278 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, d365278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, d365278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d364965 q = 1) : d365279 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, d365279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, d365279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d364965 q = 1) : d365280 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, d365280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, d365280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100704 (p : Pattern) (ha : d310047 p = 1) (hb : d364965 p = 1) : d365286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d364965 q = 1) : d365281 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, d365281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100703 q ha hb
    | true =>
      simp only [d310042, d365281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d364965 q = 1) : d365282 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, d365282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, d365282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d364965 q = 1) : d365283 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, d365283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, d365283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d364965 q = 1) : d365284 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, d365284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, d365284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d364965 q = 1) : d365285 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, d365285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, d365285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d364965 q = 1) : d365286 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, d365286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, d365286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100705 (p : Pattern) (ha : d310053 p = 1) (hb : d364965 p = 1) : d365292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d364965 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d364965 q = 1) : d365287 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, d365287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100704 q ha hb
    | true =>
      simp only [d310048, d365287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d364965 q = 1) : d365288 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, d365288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, d365288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d364965 q = 1) : d365289 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, d365289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, d365289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d364965 q = 1) : d365290 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, d365290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, d365290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d364965 q = 1) : d365291 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, d365291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, d365291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d364965 q = 1) : d365292 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, d365292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, d365292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro100706 (p : Pattern) (ha : d361211 p = 1) (hb : d365070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361206 q = 1) (hb : d365060 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361206, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100549 q ha hb
    | true =>
      simp only [d361206, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361207 q = 1) (hb : d365061 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361207, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361207, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361208 q = 1) (hb : d365062 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361208, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361208, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361209 q = 1) (hb : d365064 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361209, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361209, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361210 q = 1) (hb : d365069 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361210, d365069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361210, d365069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361211 q = 1) (hb : d365070 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361211, d365070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361211, d365070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100707 (p : Pattern) (ha : d361217 p = 1) (hb : d365080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361214 q = 1) (hb : d365077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361215 q = 1) (hb : d365078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361215, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361215, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361216 q = 1) (hb : d365079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361216, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361216, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361217 q = 1) (hb : d365080 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361217, d365080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361217, d365080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100708 (p : Pattern) (ha : d361224 p = 1) (hb : d365090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361214 q = 1) (hb : d365077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361215 q = 1) (hb : d365078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361215, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361215, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361216 q = 1) (hb : d365079 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361216, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361216, d365079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361224 q = 1) (hb : d365090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361224, d365090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361224, d365090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100709 (p : Pattern) (ha : d361286 p = 1) (hb : d365170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361275 q = 1) (hb : d365160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361275, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361275, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361276 q = 1) (hb : d365161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361276, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361276, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361277 q = 1) (hb : d365162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361277, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361277, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361278 q = 1) (hb : d365163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361278, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361278, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361225 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
    | true =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361282 q = 1) (hb : d365166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361282, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361282, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361283 q = 1) (hb : d365167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361283, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361283, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361284 q = 1) (hb : d365168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361284, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361284, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361285 q = 1) (hb : d365169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361285, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361285, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361286 q = 1) (hb : d365170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361286, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361286, d365170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100710 (p : Pattern) (ha : d361322 p = 1) (hb : d365066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361317 q = 1) (hb : d364541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100551 q ha hb
    | true =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100549 q ha hb
  have h2 (q : Pattern) (ha : d361318 q = 1) (hb : d364542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361319 q = 1) (hb : d364543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361206 q = 1) (hb : d365060 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361206, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100549 q ha hb
    | true =>
      simp only [d361206, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361207 q = 1) (hb : d365061 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361207, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361207, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361208 q = 1) (hb : d365062 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361208, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361208, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361320 q = 1) (hb : d365063 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361320, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361320, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361209 q = 1) (hb : d365064 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361209, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361209, d365064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361321 q = 1) (hb : d365065 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361321, d365065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361321, d365065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361322 q = 1) (hb : d365066 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361322, d365066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361322, d365066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100711 (p : Pattern) (ha : d361328 p = 1) (hb : d365076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361325 q = 1) (hb : d365073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361326 q = 1) (hb : d365074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361326, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361326, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361327 q = 1) (hb : d365075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361327, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361327, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361328 q = 1) (hb : d365076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361328, d365076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361328, d365076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100712 (p : Pattern) (ha : d361404 p = 1) (hb : d365086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361329 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
    | true =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
  have h2 (q : Pattern) (ha : d361400 q = 1) (hb : d365082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361400, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361400, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361401 q = 1) (hb : d365083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361401, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361401, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361402 q = 1) (hb : d365084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361402, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361402, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361403 q = 1) (hb : d365085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361403, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361403, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361404 q = 1) (hb : d365086 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361404, d365086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361404, d365086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100713 (p : Pattern) (ha : d361344 p = 1) (hb : d365089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361325 q = 1) (hb : d365073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361326 q = 1) (hb : d365074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361326, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361326, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361327 q = 1) (hb : d365075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361327, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361327, d365075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361344 q = 1) (hb : d365089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361344, d365089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361344, d365089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100714 (p : Pattern) (ha : d361411 p = 1) (hb : d365096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361329 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
    | true =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
  have h2 (q : Pattern) (ha : d361400 q = 1) (hb : d365082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361400, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361400, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361401 q = 1) (hb : d365083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361401, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361401, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361402 q = 1) (hb : d365084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361402, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361402, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361403 q = 1) (hb : d365085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361403, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361403, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361345 q = 1) (hb : d365091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100713 q ha hb
    | true =>
      simp only [d361345, d365091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
  have h7 (q : Pattern) (ha : d361407 q = 1) (hb : d365092 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361407, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361407, d365092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361408 q = 1) (hb : d365093 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361408, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361408, d365093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361409 q = 1) (hb : d365094 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361409, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361409, d365094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361410 q = 1) (hb : d365095 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361410, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361410, d365095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361411 q = 1) (hb : d365096 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361411, d365096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361411, d365096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100715 (p : Pattern) (ha : d361291 p = 1) (hb : d365103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361214 q = 1) (hb : d365077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361215 q = 1) (hb : d365078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361215, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361215, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361290 q = 1) (hb : d365102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361290, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361290, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361291 q = 1) (hb : d365103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361291, d365103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361291, d365103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100716 (p : Pattern) (ha : d361298 p = 1) (hb : d365113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361214 q = 1) (hb : d365077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361296 q = 1) (hb : d365111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361296, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361296, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361297 q = 1) (hb : d365112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361297, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361297, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361298 q = 1) (hb : d365113 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361298, d365113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361298, d365113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100717 (p : Pattern) (ha : d361416 p = 1) (hb : d365101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361325 q = 1) (hb : d365073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361326 q = 1) (hb : d365074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361326, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361326, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361415 q = 1) (hb : d365100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361415, d365100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361415, d365100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361416 q = 1) (hb : d365101 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361416, d365101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361416, d365101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100718 (p : Pattern) (ha : d361423 p = 1) (hb : d365110 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361325 q = 1) (hb : d365073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361421 q = 1) (hb : d365108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361421, d365108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361421, d365108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361422 q = 1) (hb : d365109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361422, d365109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361422, d365109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361423 q = 1) (hb : d365110 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361423, d365110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361423, d365110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100719 (p : Pattern) (ha : d361455 p = 1) (hb : d365118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361450 q = 1) (hb : d364537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361450, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100553 q ha hb
    | true =>
      simp only [d361450, d364537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100551 q ha hb
  have h2 (q : Pattern) (ha : d361451 q = 1) (hb : d364538 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361451, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361451, d364538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361452 q = 1) (hb : d364539 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361452, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361452, d364539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361317 q = 1) (hb : d364541 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100551 q ha hb
    | true =>
      simp only [d361317, d364541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100549 q ha hb
  have h5 (q : Pattern) (ha : d361318 q = 1) (hb : d364542 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361318, d364542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361319 q = 1) (hb : d364543 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361319, d364543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361453 q = 1) (hb : d364544 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361453, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361453, d364544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361206 q = 1) (hb : d365060 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361206, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100549 q ha hb
    | true =>
      simp only [d361206, d365060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361207 q = 1) (hb : d365061 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361207, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361207, d365061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361208 q = 1) (hb : d365062 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361208, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361208, d365062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361320 q = 1) (hb : d365063 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361320, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361320, d365063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d361454 q = 1) (hb : d365117 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361454, d365117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361454, d365117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361455 q = 1) (hb : d365118 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361455, d365118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361455, d365118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100720 (p : Pattern) (ha : d361461 p = 1) (hb : d365124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361456 q = 1) (hb : d365119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361456, d365119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100719 q ha hb
    | true =>
      simp only [d361456, d365119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361457 q = 1) (hb : d365120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361457, d365120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361457, d365120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361458 q = 1) (hb : d365121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361458, d365121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361458, d365121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361459 q = 1) (hb : d365122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361459, d365122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361459, d365122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361460 q = 1) (hb : d365123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361460, d365123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361460, d365123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361461 q = 1) (hb : d365124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361461, d365124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361461, d365124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro100721 (p : Pattern) (ha : d361467 p = 1) (hb : d365130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361464 q = 1) (hb : d365127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361464, d365127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361464, d365127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361465 q = 1) (hb : d365128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361465, d365128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361465, d365128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361466 q = 1) (hb : d365129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361466, d365129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361466, d365129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361467 q = 1) (hb : d365130 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361467, d365130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361467, d365130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100722 (p : Pattern) (ha : d361473 p = 1) (hb : d365136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361417 q = 1) (hb : d365104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361417, d365104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100717 q ha hb
    | true =>
      simp only [d361417, d365104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100715 q ha hb
  have h2 (q : Pattern) (ha : d361418 q = 1) (hb : d365105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361418, d365105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361418, d365105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361419 q = 1) (hb : d365106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361419, d365106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361419, d365106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361420 q = 1) (hb : d365107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361420, d365107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361420, d365107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361424 q = 1) (hb : d365114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361424, d365114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100718 q ha hb
    | true =>
      simp only [d361424, d365114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100716 q ha hb
  have h6 (q : Pattern) (ha : d361425 q = 1) (hb : d365115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361425, d365115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361425, d365115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361426 q = 1) (hb : d365116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361426, d365116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361426, d365116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361462 q = 1) (hb : d365125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361462, d365125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100720 q ha hb
    | true =>
      simp only [d361462, d365125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361329 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d361463 q = 1) (hb : d365126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361463, d365126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361463, d365126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361468 q = 1) (hb : d365131 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361468, d365131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100721 q ha hb
    | true =>
      simp only [d361468, d365131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361469 q = 1) (hb : d365132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361469, d365132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361469, d365132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361470 q = 1) (hb : d365133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361470, d365133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361470, d365133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361471 q = 1) (hb : d365134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361471, d365134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361471, d365134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361472 q = 1) (hb : d365135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361472, d365135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361472, d365135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361473 q = 1) (hb : d365136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361473, d365136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361473, d365136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro100723 (p : Pattern) (ha : d361335 p = 1) (hb : d365138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361214 q = 1) (hb : d365077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361215 q = 1) (hb : d365078 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361215, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361215, d365078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361290 q = 1) (hb : d365102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361290, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361290, d365102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361335 q = 1) (hb : d365138 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361335, d365138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361335, d365138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100724 (p : Pattern) (ha : d361340 p = 1) (hb : d365144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361214 q = 1) (hb : d365077 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361214, d365077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361296 q = 1) (hb : d365111 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361296, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361296, d365111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361297 q = 1) (hb : d365112 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361297, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361297, d365112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361340 q = 1) (hb : d365144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361340, d365144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361340, d365144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100725 (p : Pattern) (ha : d361474 p = 1) (hb : d365137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361325 q = 1) (hb : d365073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361326 q = 1) (hb : d365074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361326, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361326, d365074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361415 q = 1) (hb : d365100 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361415, d365100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361415, d365100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361474 q = 1) (hb : d365137 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361474, d365137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361474, d365137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100726 (p : Pattern) (ha : d361479 p = 1) (hb : d365143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361212 q = 1) (hb : d365071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100706 q ha hb
    | true =>
      simp only [d361212, d365071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361213 q = 1) (hb : d365072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361213, d365072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361325 q = 1) (hb : d365073 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361325, d365073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361421 q = 1) (hb : d365108 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361421, d365108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361421, d365108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361422 q = 1) (hb : d365109 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361422, d365109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361422, d365109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361479 q = 1) (hb : d365143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361479, d365143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361479, d365143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100727 (p : Pattern) (ha : d361483 p = 1) (hb : d365148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361456 q = 1) (hb : d365119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361456, d365119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100719 q ha hb
    | true =>
      simp only [d361456, d365119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361457 q = 1) (hb : d365120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361457, d365120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361457, d365120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361458 q = 1) (hb : d365121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361458, d365121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361458, d365121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361459 q = 1) (hb : d365122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361459, d365122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361459, d365122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361460 q = 1) (hb : d365123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361460, d365123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361460, d365123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361483 q = 1) (hb : d365148 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361483, d365148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361483, d365148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100728 (p : Pattern) (ha : d361486 p = 1) (hb : d365151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361323 q = 1) (hb : d365067 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100710 q ha hb
    | true =>
      simp only [d361323, d365067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361324 q = 1) (hb : d365068 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361324, d365068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361464 q = 1) (hb : d365127 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361464, d365127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361464, d365127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361465 q = 1) (hb : d365128 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361465, d365128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361465, d365128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361466 q = 1) (hb : d365129 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361466, d365129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361466, d365129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361486 q = 1) (hb : d365151 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361486, d365151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361486, d365151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100729 (p : Pattern) (ha : d361492 p = 1) (hb : d365157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361417 q = 1) (hb : d365104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361417, d365104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100717 q ha hb
    | true =>
      simp only [d361417, d365104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100715 q ha hb
  have h2 (q : Pattern) (ha : d361418 q = 1) (hb : d365105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361418, d365105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361418, d365105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361419 q = 1) (hb : d365106 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361419, d365106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361419, d365106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361420 q = 1) (hb : d365107 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361420, d365107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361420, d365107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361424 q = 1) (hb : d365114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361424, d365114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100718 q ha hb
    | true =>
      simp only [d361424, d365114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100716 q ha hb
  have h6 (q : Pattern) (ha : d361425 q = 1) (hb : d365115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361425, d365115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361425, d365115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361426 q = 1) (hb : d365116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361426, d365116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361426, d365116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361462 q = 1) (hb : d365125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361462, d365125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100720 q ha hb
    | true =>
      simp only [d361462, d365125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d361329 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d361463 q = 1) (hb : d365126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361463, d365126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361463, d365126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d361468 q = 1) (hb : d365131 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361468, d365131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100721 q ha hb
    | true =>
      simp only [d361468, d365131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d361469 q = 1) (hb : d365132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361469, d365132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361469, d365132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d361470 q = 1) (hb : d365133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361470, d365133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361470, d365133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361471 q = 1) (hb : d365134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361471, d365134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361471, d365134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d361472 q = 1) (hb : d365135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361472, d365135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361472, d365135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d361475 q = 1) (hb : d365139 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361475, d365139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100725 q ha hb
    | true =>
      simp only [d361475, d365139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100723 q ha hb
  have h17 (q : Pattern) (ha : d361476 q = 1) (hb : d365140 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361476, d365140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361476, d365140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d361477 q = 1) (hb : d365141 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361477, d365141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361477, d365141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d361478 q = 1) (hb : d365142 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361478, d365142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361478, d365142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d361480 q = 1) (hb : d365145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361480, d365145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100726 q ha hb
    | true =>
      simp only [d361480, d365145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100724 q ha hb
  have h21 (q : Pattern) (ha : d361481 q = 1) (hb : d365146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361481, d365146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361481, d365146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d361482 q = 1) (hb : d365147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361482, d365147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361482, d365147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d361484 q = 1) (hb : d365149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361484, d365149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100727 q ha hb
    | true =>
      simp only [d361484, d365149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100713 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d361345 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d361485 q = 1) (hb : d365150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361485, d365150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d361485, d365150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d361487 q = 1) (hb : d365152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361487, d365152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100728 q ha hb
    | true =>
      simp only [d361487, d365152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d361488 q = 1) (hb : d365153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361488, d365153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d361488, d365153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d361489 q = 1) (hb : d365154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361489, d365154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d361489, d365154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d361490 q = 1) (hb : d365155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361490, d365155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d361490, d365155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d361491 q = 1) (hb : d365156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361491, d365156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361491, d365156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d361492 q = 1) (hb : d365157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361492, d365157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d361492, d365157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro100730 (p : Pattern) (ha : d361494 p = 1) (hb : d365164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361329 q = 1) (hb : d365081 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100711 q ha hb
    | true =>
      simp only [d361329, d365081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
  have h2 (q : Pattern) (ha : d361400 q = 1) (hb : d365082 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361400, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361400, d365082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361401 q = 1) (hb : d365083 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361401, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361401, d365083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361402 q = 1) (hb : d365084 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361402, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361402, d365084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361403 q = 1) (hb : d365085 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361403, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361403, d365085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361218 q = 1) (hb : d365159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100707 q ha hb
    | true =>
      simp only [d361218, d365159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361275 q = 1) (hb : d365160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361275, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361275, d365160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361276 q = 1) (hb : d365161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361276, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361276, d365161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361277 q = 1) (hb : d365162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361277, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361277, d365162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361278 q = 1) (hb : d365163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361278, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361278, d365163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361494 q = 1) (hb : d365164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361494, d365164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361494, d365164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro100731 (p : Pattern) (ha : d361501 p = 1) (hb : d365177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361484 q = 1) (hb : d365149 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361484, d365149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100727 q ha hb
    | true =>
      simp only [d361484, d365149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100713 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361345 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361485 q = 1) (hb : d365150 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361485, d365150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361485, d365150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d361487 q = 1) (hb : d365152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361487, d365152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100728 q ha hb
    | true =>
      simp only [d361487, d365152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361488 q = 1) (hb : d365153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361488, d365153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361488, d365153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361489 q = 1) (hb : d365154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361489, d365154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361489, d365154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361499 q = 1) (hb : d365175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361499, d365175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361499, d365175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361500 q = 1) (hb : d365176 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361500, d365176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361500, d365176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361501 q = 1) (hb : d365177 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361501, d365177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361501, d365177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100732 (p : Pattern) (ha : d361503 p = 1) (hb : d365179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361225 q = 1) (hb : d365165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100708 q ha hb
    | true =>
      simp only [d361225, d365165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361282 q = 1) (hb : d365166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361282, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361282, d365166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361283 q = 1) (hb : d365167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361283, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361283, d365167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361284 q = 1) (hb : d365168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361284, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361284, d365168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361285 q = 1) (hb : d365169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361285, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361285, d365169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361503 q = 1) (hb : d365179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361503, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361503, d365179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100733 (p : Pattern) (ha : d361252 p = 1) (hb : d365203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361247 q = 1) (hb : d365185 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361247, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100583 q ha hb
    | true =>
      simp only [d361247, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361248 q = 1) (hb : d365186 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361248, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361248, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361249 q = 1) (hb : d365187 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361249, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361249, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361250 q = 1) (hb : d365193 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361250, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361250, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361251 q = 1) (hb : d365202 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361251, d365202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361251, d365202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361252 q = 1) (hb : d365203 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361252, d365203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361252, d365203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100734 (p : Pattern) (ha : d361376 p = 1) (hb : d365195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361371 q = 1) (hb : d364708 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100584 q ha hb
    | true =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100583 q ha hb
  have h2 (q : Pattern) (ha : d361372 q = 1) (hb : d364709 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361373 q = 1) (hb : d364710 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361247 q = 1) (hb : d365185 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361247, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100583 q ha hb
    | true =>
      simp only [d361247, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361248 q = 1) (hb : d365186 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361248, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361248, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361249 q = 1) (hb : d365187 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361249, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361249, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361374 q = 1) (hb : d365188 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361374, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361374, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361250 q = 1) (hb : d365193 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361250, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361250, d365193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361375 q = 1) (hb : d365194 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361375, d365194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361375, d365194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361376 q = 1) (hb : d365195 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361376, d365195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d361376, d365195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro100735 (p : Pattern) (ha : d361382 p = 1) (hb : d365209 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361377 q = 1) (hb : d365196 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361377, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100734 q ha hb
    | true =>
      simp only [d361377, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361378 q = 1) (hb : d365197 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361378, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361378, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361253 q = 1) (hb : d365204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361253, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100733 q ha hb
    | true =>
      simp only [d361253, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361254 q = 1) (hb : d365205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361254, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361254, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361379 q = 1) (hb : d365206 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361379, d365206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361379, d365206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361380 q = 1) (hb : d365207 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361380, d365207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361380, d365207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361381 q = 1) (hb : d365208 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361381, d365208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361381, d365208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361382 q = 1) (hb : d365209 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361382, d365209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361382, d365209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100736 (p : Pattern) (ha : d361525 p = 1) (hb : d365190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361520 q = 1) (hb : d364704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361520, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100585 q ha hb
    | true =>
      simp only [d361520, d364704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100584 q ha hb
  have h2 (q : Pattern) (ha : d361521 q = 1) (hb : d364705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361521, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361521, d364705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361522 q = 1) (hb : d364706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361522, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361522, d364706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361371 q = 1) (hb : d364708 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100584 q ha hb
    | true =>
      simp only [d361371, d364708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100583 q ha hb
  have h5 (q : Pattern) (ha : d361372 q = 1) (hb : d364709 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361372, d364709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361373 q = 1) (hb : d364710 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361373, d364710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361523 q = 1) (hb : d364711 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361523, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361523, d364711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361247 q = 1) (hb : d365185 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d361247, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100583 q ha hb
    | true =>
      simp only [d361247, d365185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d361248 q = 1) (hb : d365186 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d361248, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361248, d365186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d361249 q = 1) (hb : d365187 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d361249, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361249, d365187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361374 q = 1) (hb : d365188 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d361374, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361374, d365188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d361524 q = 1) (hb : d365189 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d361524, d365189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361524, d365189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d361525 q = 1) (hb : d365190 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d361525, d365190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d361525, d365190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro100737 (p : Pattern) (ha : d361531 p = 1) (hb : d365201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361526 q = 1) (hb : d365191 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361526, d365191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100736 q ha hb
    | true =>
      simp only [d361526, d365191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361527 q = 1) (hb : d365192 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361527, d365192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361527, d365192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361377 q = 1) (hb : d365196 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361377, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100734 q ha hb
    | true =>
      simp only [d361377, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361378 q = 1) (hb : d365197 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361378, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361378, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361528 q = 1) (hb : d365198 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361528, d365198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361528, d365198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361529 q = 1) (hb : d365199 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361529, d365199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361529, d365199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d361530 q = 1) (hb : d365200 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361530, d365200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361530, d365200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d361531 q = 1) (hb : d365201 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361531, d365201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d361531, d365201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro100738 (p : Pattern) (ha : d361537 p = 1) (hb : d365215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361377 q = 1) (hb : d365196 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361377, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100734 q ha hb
    | true =>
      simp only [d361377, d365196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361378 q = 1) (hb : d365197 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361378, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361378, d365197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361534 q = 1) (hb : d365212 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361534, d365212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361534, d365212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361535 q = 1) (hb : d365213 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361535, d365213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361535, d365213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361536 q = 1) (hb : d365214 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361536, d365214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361536, d365214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361537 q = 1) (hb : d365215 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361537, d365215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361537, d365215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100739 (p : Pattern) (ha : d361543 p = 1) (hb : d365221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361532 q = 1) (hb : d365210 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361532, d365210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100737 q ha hb
    | true =>
      simp only [d361532, d365210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100735 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d361383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d361533 q = 1) (hb : d365211 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361533, d365211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361533, d365211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d361538 q = 1) (hb : d365216 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361538, d365216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100738 q ha hb
    | true =>
      simp only [d361538, d365216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361539 q = 1) (hb : d365217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361539, d365217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361539, d365217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361540 q = 1) (hb : d365218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361540, d365218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361540, d365218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361541 q = 1) (hb : d365219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361541, d365219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361541, d365219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d361542 q = 1) (hb : d365220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361542, d365220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361542, d365220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361543 q = 1) (hb : d365221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361543, d365221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361543, d365221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro100740 (p : Pattern) (ha : d361258 p = 1) (hb : d365226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361253 q = 1) (hb : d365204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d361253, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100733 q ha hb
    | true =>
      simp only [d361253, d365204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361254 q = 1) (hb : d365205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d361254, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361254, d365205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361255 q = 1) (hb : d365223 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d361255, d365223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361255, d365223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361256 q = 1) (hb : d365224 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d361256, d365224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361256, d365224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361257 q = 1) (hb : d365225 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d361257, d365225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d361257, d365225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d361258 q = 1) (hb : d365226 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d361258, d365226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361258, d365226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100741 (p : Pattern) (ha : d361549 p = 1) (hb : d365232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361259 q = 1) (hb : d365227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d361259, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100740 q ha hb
    | true =>
      simp only [d361259, d365227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d361545 q = 1) (hb : d365228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d361545, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361545, d365228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d361546 q = 1) (hb : d365229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d361546, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361546, d365229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d361547 q = 1) (hb : d365230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d361547, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361547, d365230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361548 q = 1) (hb : d365231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d361548, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361548, d365231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361549 q = 1) (hb : d365232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d361549, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361549, d365232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro100742 (p : Pattern) (ha : d361555 p = 1) (hb : d365238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361405 q = 1) (hb : d365087 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361405, d365087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361405, d365087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100712 q ha hb
  have h2 (q : Pattern) (ha : d361406 q = 1) (hb : d365088 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361406, d365088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d361406, d365088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d361412 q = 1) (hb : d365097 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361412, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100712 q ha hb
    | true =>
      simp only [d361412, d365097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100714 q ha hb
  have h4 (q : Pattern) (ha : d361413 q = 1) (hb : d365098 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361413, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d361413, d365098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d361414 q = 1) (hb : d365099 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361414, d365099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d361414, d365099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361493 q = 1) (hb : d365158 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361493, d365158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100722 q ha hb
    | true =>
      simp only [d361493, d365158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100729 q ha hb
  have h7 (q : Pattern) (ha : d361495 q = 1) (hb : d365171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361495, d365171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100730 q ha hb
    | true =>
      simp only [d361495, d365171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100709 q ha hb
  have h8 (q : Pattern) (ha : d361496 q = 1) (hb : d365172 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361496, d365172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d361496, d365172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d361497 q = 1) (hb : d365173 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361497, d365173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d361497, d365173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d361498 q = 1) (hb : d365174 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361498, d365174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d361498, d365174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d361502 q = 1) (hb : d365178 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361502, d365178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361502, d365178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100731 q ha hb
  have h12 (q : Pattern) (ha : d361504 q = 1) (hb : d365180 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361504, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361504, d365180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100732 q ha hb
  have h13 (q : Pattern) (ha : d361505 q = 1) (hb : d365181 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361505, d365181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d361505, d365181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d361506 q = 1) (hb : d365182 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361506, d365182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d361506, d365182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d361507 q = 1) (hb : d365183 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361507, d365183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d361507, d365183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d361508 q = 1) (hb : d365184 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361508, d365184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d361508, d365184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d361544 q = 1) (hb : d365222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361544, d365222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361544, d365222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100739 q ha hb
  have h18 (q : Pattern) (ha : d361550 q = 1) (hb : d365233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d361550, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361550, d365233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100741 q ha hb
  have h19 (q : Pattern) (ha : d361551 q = 1) (hb : d365234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d361551, d365234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d361551, d365234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d361552 q = 1) (hb : d365235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d361552, d365235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d361552, d365235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d361553 q = 1) (hb : d365236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d361553, d365236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d361553, d365236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d361554 q = 1) (hb : d365237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d361554, d365237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d361554, d365237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d361555 q = 1) (hb : d365238 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d361555, d365238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d361555, d365238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro100743 (p : Pattern) (ha : d361561 p = 1) (hb : d365244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361399 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d361556 q = 1) (hb : d365239 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d361556, d365239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361556, d365239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100742 q ha hb
  have h3 (q : Pattern) (ha : d361557 q = 1) (hb : d365240 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d361557, d365240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361557, d365240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d361558 q = 1) (hb : d365241 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d361558, d365241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361558, d365241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d361559 q = 1) (hb : d365242 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d361559, d365242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361559, d365242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d361560 q = 1) (hb : d365243 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d361560, d365243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d361560, d365243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d361561 q = 1) (hb : d365244 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d361561, d365244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d361561, d365244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro100744 (p : Pattern) (ha : d365017 p = 1) (hb : d365250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d361561 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d361561 q = 1) (hb : d365245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d365245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d365245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100743 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d365013 q = 1) (hb : d365246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d365013, d365246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365013, d365246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d365014 q = 1) (hb : d365247 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d365014, d365247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365014, d365247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d365015 q = 1) (hb : d365248 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d365015, d365248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365015, d365248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d365016 q = 1) (hb : d365249 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d365016, d365249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365016, d365249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d365017 q = 1) (hb : d365250 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d365017, d365250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d365017, d365250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro100745 (p : Pattern) (ha : d365023 p = 1) (hb : d365256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365018 q = 1) (hb : d365251 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d365018, d365251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100744 q ha hb
    | true =>
      simp only [d365018, d365251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365019 q = 1) (hb : d365252 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d365019, d365252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365019, d365252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365020 q = 1) (hb : d365253 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d365020, d365253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365020, d365253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365021 q = 1) (hb : d365254 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d365021, d365254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365021, d365254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365022 q = 1) (hb : d365255 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d365022, d365255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365022, d365255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365023 q = 1) (hb : d365256 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d365023, d365256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365023, d365256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100746 (p : Pattern) (ha : d365029 p = 1) (hb : d365262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365024 q = 1) (hb : d365257 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d365024, d365257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100745 q ha hb
    | true =>
      simp only [d365024, d365257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365025 q = 1) (hb : d365258 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d365025, d365258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365025, d365258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365026 q = 1) (hb : d365259 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d365026, d365259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365026, d365259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365027 q = 1) (hb : d365260 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d365027, d365260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365027, d365260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365028 q = 1) (hb : d365261 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d365028, d365261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365028, d365261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365029 q = 1) (hb : d365262 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d365029, d365262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365029, d365262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100747 (p : Pattern) (ha : d365035 p = 1) (hb : d365268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365030 q = 1) (hb : d365263 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d365030, d365263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100746 q ha hb
    | true =>
      simp only [d365030, d365263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365031 q = 1) (hb : d365264 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d365031, d365264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365031, d365264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365032 q = 1) (hb : d365265 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d365032, d365265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365032, d365265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365033 q = 1) (hb : d365266 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d365033, d365266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365033, d365266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365034 q = 1) (hb : d365267 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d365034, d365267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365034, d365267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365035 q = 1) (hb : d365268 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d365035, d365268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365035, d365268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100748 (p : Pattern) (ha : d365041 p = 1) (hb : d365274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365036 q = 1) (hb : d365269 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d365036, d365269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100747 q ha hb
    | true =>
      simp only [d365036, d365269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365037 q = 1) (hb : d365270 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d365037, d365270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365037, d365270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365038 q = 1) (hb : d365271 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d365038, d365271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365038, d365271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365039 q = 1) (hb : d365272 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d365039, d365272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365039, d365272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365040 q = 1) (hb : d365273 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d365040, d365273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365040, d365273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365041 q = 1) (hb : d365274 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d365041, d365274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365041, d365274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro100749 (p : Pattern) (ha : d365047 p = 1) (hb : d365280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d365042 q = 1) (hb : d365275 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d365042, d365275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100748 q ha hb
    | true =>
      simp only [d365042, d365275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d365043 q = 1) (hb : d365276 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d365043, d365276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d365043, d365276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d365044 q = 1) (hb : d365277 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d365044, d365277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d365044, d365277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d365045 q = 1) (hb : d365278 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d365045, d365278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d365045, d365278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d365046 q = 1) (hb : d365279 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d365046, d365279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d365046, d365279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d365047 q = 1) (hb : d365280 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d365047, d365280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d365047, d365280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
