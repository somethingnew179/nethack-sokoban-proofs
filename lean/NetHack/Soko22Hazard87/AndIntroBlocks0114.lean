import NetHack.Soko22Hazard87.AndIntroBlocks0113
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro28500 (p : Pattern) (ha : d115270 p = 1) (hb : d115574 p = 1) : d115627 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d115574 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115248 q = 1) (hb : d115574 q = 1) : d115596 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115248, d115596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28493 q ha hb
    | true =>
      simp only [d115248, d115596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28495 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d115574 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115249 q = 1) (hb : d115574 q = 1) : d115597 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115249, d115597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115249, d115597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115250 q = 1) (hb : d115574 q = 1) : d115598 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115250, d115598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115250, d115598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115251 q = 1) (hb : d115574 q = 1) : d115599 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115251, d115599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115251, d115599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115255 q = 1) (hb : d115574 q = 1) : d115603 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115255, d115603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115255, d115603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28496 q ha hb
  have h8 (q : Pattern) (ha : d115256 q = 1) (hb : d115574 q = 1) : d115604 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115256, d115604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115256, d115604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d115257 q = 1) (hb : d115574 q = 1) : d115605 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115257, d115605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115257, d115605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d115258 q = 1) (hb : d115574 q = 1) : d115606 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115258, d115606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115258, d115606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115259 q = 1) (hb : d115574 q = 1) : d115607 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115259, d115607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115259, d115607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115265 q = 1) (hb : d115574 q = 1) : d115622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115265, d115622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115265, d115622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28499 q ha hb
  have h13 (q : Pattern) (ha : d115266 q = 1) (hb : d115574 q = 1) : d115623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115266, d115623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115266, d115623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d115267 q = 1) (hb : d115574 q = 1) : d115624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115267, d115624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115267, d115624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d115268 q = 1) (hb : d115574 q = 1) : d115625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115268, d115625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115268, d115625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d115269 q = 1) (hb : d115574 q = 1) : d115626 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115269, d115626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115269, d115626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115270 q = 1) (hb : d115574 q = 1) : d115627 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115270, d115627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115270, d115627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28501 (p : Pattern) (ha : d12289 p = 1) (hb : d115574 p = 1) : d115637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28492 q ha hb
    | true =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d115574 q = 1) : d115633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d115574 q = 1) : d115634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d115574 q = 1) : d115635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d115574 q = 1) : d115636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12289 q = 1) (hb : d115574 q = 1) : d115637 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12289, d115637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12289, d115637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28502 (p : Pattern) (ha : d12296 p = 1) (hb : d115574 p = 1) : d115644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28492 q ha hb
    | true =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d115574 q = 1) : d115633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d115574 q = 1) : d115634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d115574 q = 1) : d115635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d115574 q = 1) : d115636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d115574 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12241 q = 1) (hb : d115574 q = 1) : d115590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28494 q ha hb
    | true =>
      simp only [d12241, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12292 q = 1) (hb : d115574 q = 1) : d115640 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12293 q = 1) (hb : d115574 q = 1) : d115641 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12293, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12294 q = 1) (hb : d115574 q = 1) : d115642 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12295 q = 1) (hb : d115574 q = 1) : d115643 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12296 q = 1) (hb : d115574 q = 1) : d115644 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12296, d115644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12296, d115644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro28503 (p : Pattern) (ha : d12373 p = 1) (hb : d115574 p = 1) : d115701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d115574 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12234 q = 1) (hb : d115574 q = 1) : d115583 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28492 q ha hb
    | true =>
      simp only [d12234, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12285 q = 1) (hb : d115574 q = 1) : d115633 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12285, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12286 q = 1) (hb : d115574 q = 1) : d115634 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12286, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12287 q = 1) (hb : d115574 q = 1) : d115635 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12287, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12288 q = 1) (hb : d115574 q = 1) : d115636 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12288, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d115574 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12373 q = 1) (hb : d115574 q = 1) : d115701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12373, d115701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12373, d115701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28504 (p : Pattern) (ha : d12301 p = 1) (hb : d115574 p = 1) : d115649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d115574 q = 1) : d115580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12300 q = 1) (hb : d115574 q = 1) : d115648 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12301 q = 1) (hb : d115574 q = 1) : d115649 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12301, d115649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12301, d115649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28505 (p : Pattern) (ha : d12308 p = 1) (hb : d115574 p = 1) : d115656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12306 q = 1) (hb : d115574 q = 1) : d115654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12307 q = 1) (hb : d115574 q = 1) : d115655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12307, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12308 q = 1) (hb : d115574 q = 1) : d115656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12308, d115656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12308, d115656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28506 (p : Pattern) (ha : d12318 p = 1) (hb : d115574 p = 1) : d115662 p = 1 := by
  have h0 (q : Pattern) (ha : d12315 q = 1) (hb : d94753 q = 1) : d12315 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4821 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12316 q = 1) (hb : d115574 q = 1) : d115660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12316, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d94753 q = 1) : d4821 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12225 q = 1) (hb : d115574 q = 1) : d4822 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12225, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12225, d115574, d4822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d12317 q = 1) (hb : d115574 q = 1) : d115661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12317, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12317, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12318 q = 1) (hb : d115574 q = 1) : d115662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12318, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12318, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28507 (p : Pattern) (ha : d12324 p = 1) (hb : d115574 p = 1) : d115668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28506 q ha hb
    | true =>
      simp only [d12319, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d115574 q = 1) : d115665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d115574 q = 1) : d115666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d115574 q = 1) : d115667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12324 q = 1) (hb : d115574 q = 1) : d115668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12324, d115668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12324, d115668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28508 (p : Pattern) (ha : d12344 p = 1) (hb : d115574 p = 1) : d115674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d115574 q = 1) : d115671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d115574 q = 1) : d115672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d115574 q = 1) : d115673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12344 q = 1) (hb : d115574 q = 1) : d115674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12344, d115674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12344, d115674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28509 (p : Pattern) (ha : d115280 p = 1) (hb : d115574 p = 1) : d115680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d115574 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12302 q = 1) (hb : d115574 q = 1) : d115650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28504 q ha hb
    | true =>
      simp only [d12302, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12303 q = 1) (hb : d115574 q = 1) : d115651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12304 q = 1) (hb : d115574 q = 1) : d115652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12304, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12305 q = 1) (hb : d115574 q = 1) : d115653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d115574 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12309 q = 1) (hb : d115574 q = 1) : d115657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28505 q ha hb
    | true =>
      simp only [d12309, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12310 q = 1) (hb : d115574 q = 1) : d115658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12311 q = 1) (hb : d115574 q = 1) : d115659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12311, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12325 q = 1) (hb : d115574 q = 1) : d115669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28507 q ha hb
    | true =>
      simp only [d12325, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28492 q ha hb
  have h11 (q : Pattern) (ha : d115276 q = 1) (hb : d115574 q = 1) : d115670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115276, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12345 q = 1) (hb : d115574 q = 1) : d115675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28508 q ha hb
    | true =>
      simp only [d12345, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12346 q = 1) (hb : d115574 q = 1) : d115676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12346, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115277 q = 1) (hb : d115574 q = 1) : d115677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115277, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115278 q = 1) (hb : d115574 q = 1) : d115678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115278, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115279 q = 1) (hb : d115574 q = 1) : d115679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115279, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115280 q = 1) (hb : d115574 q = 1) : d115680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d115680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d115680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28510 (p : Pattern) (ha : d12351 p = 1) (hb : d115574 p = 1) : d115681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12231 q = 1) (hb : d115574 q = 1) : d115580 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12231, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12231, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12300 q = 1) (hb : d115574 q = 1) : d115648 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12300, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12300, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12351 q = 1) (hb : d115574 q = 1) : d115681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12351, d115681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12351, d115681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28511 (p : Pattern) (ha : d12356 p = 1) (hb : d115574 p = 1) : d115686 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d115574 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12230 q = 1) (hb : d115574 q = 1) : d115579 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12230, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12306 q = 1) (hb : d115574 q = 1) : d115654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12306, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12306, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12307 q = 1) (hb : d115574 q = 1) : d115655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12307, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12307, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12356 q = 1) (hb : d115574 q = 1) : d115686 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12356, d115686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12356, d115686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28512 (p : Pattern) (ha : d12360 p = 1) (hb : d115574 p = 1) : d115690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12319 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12319, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28506 q ha hb
    | true =>
      simp only [d12319, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12320 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12320, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12320, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12321 q = 1) (hb : d115574 q = 1) : d115665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12321, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12321, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12322 q = 1) (hb : d115574 q = 1) : d115666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12322, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12322, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12323 q = 1) (hb : d115574 q = 1) : d115667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12323, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12323, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12360 q = 1) (hb : d115574 q = 1) : d115690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12360, d115690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12360, d115690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28513 (p : Pattern) (ha : d12365 p = 1) (hb : d115574 p = 1) : d115693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12228 q = 1) (hb : d115574 q = 1) : d115577 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28491 q ha hb
    | true =>
      simp only [d12228, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12229 q = 1) (hb : d115574 q = 1) : d115578 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12229, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12341 q = 1) (hb : d115574 q = 1) : d115671 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12341, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12341, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12342 q = 1) (hb : d115574 q = 1) : d115672 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12342, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12342, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12343 q = 1) (hb : d115574 q = 1) : d115673 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12343, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12343, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12365 q = 1) (hb : d115574 q = 1) : d115693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12365, d115693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12365, d115693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28514 (p : Pattern) (ha : d115285 p = 1) (hb : d115574 p = 1) : d115699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d115574 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12302 q = 1) (hb : d115574 q = 1) : d115650 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12302, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28504 q ha hb
    | true =>
      simp only [d12302, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12303 q = 1) (hb : d115574 q = 1) : d115651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12303, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12303, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12304 q = 1) (hb : d115574 q = 1) : d115652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12304, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12304, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12305 q = 1) (hb : d115574 q = 1) : d115653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12305, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12305, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d115574 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12309 q = 1) (hb : d115574 q = 1) : d115657 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12309, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28505 q ha hb
    | true =>
      simp only [d12309, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12310 q = 1) (hb : d115574 q = 1) : d115658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12310, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12310, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12311 q = 1) (hb : d115574 q = 1) : d115659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12311, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12311, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12325 q = 1) (hb : d115574 q = 1) : d115669 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12325, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28507 q ha hb
    | true =>
      simp only [d12325, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28492 q ha hb
  have h11 (q : Pattern) (ha : d115276 q = 1) (hb : d115574 q = 1) : d115670 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115276, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12345 q = 1) (hb : d115574 q = 1) : d115675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12345, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28508 q ha hb
    | true =>
      simp only [d12345, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12346 q = 1) (hb : d115574 q = 1) : d115676 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12346, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12346, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115277 q = 1) (hb : d115574 q = 1) : d115677 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115277, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115278 q = 1) (hb : d115574 q = 1) : d115678 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115278, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115279 q = 1) (hb : d115574 q = 1) : d115679 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115279, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d115574 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12352 q = 1) (hb : d115574 q = 1) : d115682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12352, d115682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28510 q ha hb
    | true =>
      simp only [d12352, d115682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12353 q = 1) (hb : d115574 q = 1) : d115683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12353, d115683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12353, d115683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12354 q = 1) (hb : d115574 q = 1) : d115684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12354, d115684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12354, d115684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12355 q = 1) (hb : d115574 q = 1) : d115685 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12355, d115685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12355, d115685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d115574 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12357 q = 1) (hb : d115574 q = 1) : d115687 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12357, d115687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28511 q ha hb
    | true =>
      simp only [d12357, d115687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12358 q = 1) (hb : d115574 q = 1) : d115688 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12358, d115688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12358, d115688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12359 q = 1) (hb : d115574 q = 1) : d115689 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12359, d115689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12359, d115689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12361 q = 1) (hb : d115574 q = 1) : d115691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28512 q ha hb
    | true =>
      simp only [d12361, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28494 q ha hb
  have h27 (q : Pattern) (ha : d115281 q = 1) (hb : d115574 q = 1) : d115692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115281, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d12366 q = 1) (hb : d115574 q = 1) : d115694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28513 q ha hb
    | true =>
      simp only [d12366, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12367 q = 1) (hb : d115574 q = 1) : d115695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12367, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115282 q = 1) (hb : d115574 q = 1) : d115696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115282, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115283 q = 1) (hb : d115574 q = 1) : d115697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d115697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115283, d115697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115284 q = 1) (hb : d115574 q = 1) : d115698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d115698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115284, d115698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115285 q = 1) (hb : d115574 q = 1) : d115699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d115699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115285, d115699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro28515 (p : Pattern) (ha : d115292 p = 1) (hb : d115574 p = 1) : d115708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12361 q = 1) (hb : d115574 q = 1) : d115691 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12361, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28512 q ha hb
    | true =>
      simp only [d12361, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28494 q ha hb
  have h2 (q : Pattern) (ha : d115281 q = 1) (hb : d115574 q = 1) : d115692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115281, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12366 q = 1) (hb : d115574 q = 1) : d115694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12366, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28513 q ha hb
    | true =>
      simp only [d12366, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12367 q = 1) (hb : d115574 q = 1) : d115695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12367, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12367, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d115574 q = 1) : d115696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115282, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d115574 q = 1) : d115706 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d115706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d115706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d115574 q = 1) : d115707 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d115707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d115707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d115574 q = 1) : d115708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d115708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d115708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28516 (p : Pattern) (ha : d12392 p = 1) (hb : d115574 p = 1) : d115716 p = 1 := by
  have h0 (q : Pattern) (ha : d12389 q = 1) (hb : d94753 q = 1) : d12389 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12390 q = 1) (hb : d115574 q = 1) : d115714 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d115574, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12390, d115574, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d94753 q = 1) : d6081 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12259 q = 1) (hb : d115574 q = 1) : d6082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12259, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12259, d115574, d6082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d12391 q = 1) (hb : d115574 q = 1) : d115715 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12391, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12391, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12392 q = 1) (hb : d115574 q = 1) : d115716 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12392, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12392, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28517 (p : Pattern) (ha : d12398 p = 1) (hb : d115574 p = 1) : d115722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12393 q = 1) (hb : d115574 q = 1) : d115717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12393, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28516 q ha hb
    | true =>
      simp only [d12393, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12394 q = 1) (hb : d115574 q = 1) : d115718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12394, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12394, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12262 q = 1) (hb : d115574 q = 1) : d115610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28497 q ha hb
    | true =>
      simp only [d12262, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12263 q = 1) (hb : d115574 q = 1) : d115611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12395 q = 1) (hb : d115574 q = 1) : d115719 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12395, d115719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12395, d115719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12396 q = 1) (hb : d115574 q = 1) : d115720 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12396, d115720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12396, d115720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12397 q = 1) (hb : d115574 q = 1) : d115721 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12397, d115721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12397, d115721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12398 q = 1) (hb : d115574 q = 1) : d115722 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12398, d115722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12398, d115722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28518 (p : Pattern) (ha : d12418 p = 1) (hb : d115574 p = 1) : d115728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12262 q = 1) (hb : d115574 q = 1) : d115610 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12262, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28497 q ha hb
    | true =>
      simp only [d12262, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12263 q = 1) (hb : d115574 q = 1) : d115611 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12263, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12263, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12415 q = 1) (hb : d115574 q = 1) : d115725 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12415, d115725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12415, d115725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12416 q = 1) (hb : d115574 q = 1) : d115726 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12416, d115726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12416, d115726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12417 q = 1) (hb : d115574 q = 1) : d115727 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12417, d115727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12417, d115727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12418 q = 1) (hb : d115574 q = 1) : d115728 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12418, d115728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12418, d115728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28519 (p : Pattern) (ha : d115302 p = 1) (hb : d115574 p = 1) : d115734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12399 q = 1) (hb : d115574 q = 1) : d115723 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12399, d115723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28517 q ha hb
    | true =>
      simp only [d12399, d115723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28498 q ha hb
  have h2 (q : Pattern) (ha : d115298 q = 1) (hb : d115574 q = 1) : d115724 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d115724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115298, d115724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12419 q = 1) (hb : d115574 q = 1) : d115729 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12419, d115729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28518 q ha hb
    | true =>
      simp only [d12419, d115729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12420 q = 1) (hb : d115574 q = 1) : d115730 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12420, d115730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12420, d115730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d115574 q = 1) : d115731 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d115731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115299, d115731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d115574 q = 1) : d115732 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d115732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d115732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d115574 q = 1) : d115733 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d115733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d115733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d115574 q = 1) : d115734 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d115734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d115734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28520 (p : Pattern) (ha : d115308 p = 1) (hb : d115574 p = 1) : d115740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12290 q = 1) (hb : d115574 q = 1) : d115638 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12290, d115638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12290, d115638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28501 q ha hb
  have h2 (q : Pattern) (ha : d12291 q = 1) (hb : d115574 q = 1) : d115639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12291, d115639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12291, d115639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12297 q = 1) (hb : d115574 q = 1) : d115645 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d115645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28501 q ha hb
    | true =>
      simp only [d12297, d115645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28502 q ha hb
  have h4 (q : Pattern) (ha : d12298 q = 1) (hb : d115574 q = 1) : d115646 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d115646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12298, d115646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12299 q = 1) (hb : d115574 q = 1) : d115647 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12299, d115647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12299, d115647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115286 q = 1) (hb : d115574 q = 1) : d115700 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d115700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28509 q ha hb
    | true =>
      simp only [d115286, d115700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28514 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d115574 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12374 q = 1) (hb : d115574 q = 1) : d115702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12374, d115702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28503 q ha hb
    | true =>
      simp only [d12374, d115702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115287 q = 1) (hb : d115574 q = 1) : d115703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d115703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115287, d115703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115288 q = 1) (hb : d115574 q = 1) : d115704 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d115704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115288, d115704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115289 q = 1) (hb : d115574 q = 1) : d115705 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d115705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115289, d115705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115293 q = 1) (hb : d115574 q = 1) : d115709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d115709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115293, d115709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28515 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d115574 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115294 q = 1) (hb : d115574 q = 1) : d115710 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d115710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115294, d115710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115295 q = 1) (hb : d115574 q = 1) : d115711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d115711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115295, d115711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115296 q = 1) (hb : d115574 q = 1) : d115712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d115712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115296, d115712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115297 q = 1) (hb : d115574 q = 1) : d115713 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d115713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115297, d115713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115303 q = 1) (hb : d115574 q = 1) : d115735 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d115735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115303, d115735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28519 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d115574 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115304 q = 1) (hb : d115574 q = 1) : d115736 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d115736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115304, d115736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115305 q = 1) (hb : d115574 q = 1) : d115737 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d115737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115305, d115737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115306 q = 1) (hb : d115574 q = 1) : d115738 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d115738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115306, d115738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115307 q = 1) (hb : d115574 q = 1) : d115739 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d115739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115307, d115739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115308 q = 1) (hb : d115574 q = 1) : d115740 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d115740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115308, d115740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro28521 (p : Pattern) (ha : d115314 p = 1) (hb : d115574 p = 1) : d115746 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d115574 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115271 q = 1) (hb : d115574 q = 1) : d115628 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115271, d115628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115271, d115628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28500 q ha hb
  have h3 (q : Pattern) (ha : d115272 q = 1) (hb : d115574 q = 1) : d115629 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115272, d115629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115272, d115629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115273 q = 1) (hb : d115574 q = 1) : d115630 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115273, d115630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115273, d115630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115274 q = 1) (hb : d115574 q = 1) : d115631 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115274, d115631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115274, d115631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115275 q = 1) (hb : d115574 q = 1) : d115632 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115275, d115632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115275, d115632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115309 q = 1) (hb : d115574 q = 1) : d115741 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d115741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115309, d115741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28520 q ha hb
  have h8 (q : Pattern) (ha : d115310 q = 1) (hb : d115574 q = 1) : d115742 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d115742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115310, d115742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115311 q = 1) (hb : d115574 q = 1) : d115743 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d115743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115311, d115743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115312 q = 1) (hb : d115574 q = 1) : d115744 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d115744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115312, d115744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115313 q = 1) (hb : d115574 q = 1) : d115745 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d115745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115313, d115745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115314 q = 1) (hb : d115574 q = 1) : d115746 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d115746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115314, d115746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro28522 (p : Pattern) (ha : d12438 p = 1) (hb : d115574 p = 1) : d115662 p = 1 := by
  have h0 (q : Pattern) (ha : d12315 q = 1) (hb : d94753 q = 1) : d12315 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4821 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12316 q = 1) (hb : d115574 q = 1) : d115660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12316, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d4822 q = 1) (hb : d115574 q = 1) : d4822 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12437 q = 1) (hb : d115574 q = 1) : d115661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12437, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12437, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12438 q = 1) (hb : d115574 q = 1) : d115662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12438, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12438, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28523 (p : Pattern) (ha : d12448 p = 1) (hb : d115574 p = 1) : d115750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d115574 q = 1) : d115748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12447 q = 1) (hb : d115574 q = 1) : d115749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12447, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12448 q = 1) (hb : d115574 q = 1) : d115750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12448, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12448, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28524 (p : Pattern) (ha : d12458 p = 1) (hb : d115574 p = 1) : d115756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d115574 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d115574 q = 1) : d115751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28523 q ha hb
    | true =>
      simp only [d12453, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d115574 q = 1) : d115752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d115574 q = 1) : d115753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d115574 q = 1) : d115754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d115574 q = 1) : d115755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12458 q = 1) (hb : d115574 q = 1) : d115756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12458, d115756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12458, d115756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28525 (p : Pattern) (ha : d12461 p = 1) (hb : d115574 p = 1) : d115759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d115574 q = 1) : d115748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12447 q = 1) (hb : d115574 q = 1) : d115749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12447, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12447, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12461 q = 1) (hb : d115574 q = 1) : d115759 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12461, d115759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12461, d115759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28526 (p : Pattern) (ha : d12468 p = 1) (hb : d115574 p = 1) : d115765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d115574 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d115574 q = 1) : d115751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28523 q ha hb
    | true =>
      simp only [d12453, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d115574 q = 1) : d115752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d115574 q = 1) : d115753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d115574 q = 1) : d115754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d115574 q = 1) : d115755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12462 q = 1) (hb : d115574 q = 1) : d12462 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12463 q = 1) (hb : d115574 q = 1) : d115760 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d115760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28525 q ha hb
    | true =>
      simp only [d12463, d115760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12464 q = 1) (hb : d115574 q = 1) : d115761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12465 q = 1) (hb : d115574 q = 1) : d115762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12465, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12466 q = 1) (hb : d115574 q = 1) : d115763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12467 q = 1) (hb : d115574 q = 1) : d115764 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12468 q = 1) (hb : d115574 q = 1) : d115765 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12468, d115765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12468, d115765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro28527 (p : Pattern) (ha : d12574 p = 1) (hb : d115574 p = 1) : d115822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12452 q = 1) (hb : d115574 q = 1) : d12452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12453 q = 1) (hb : d115574 q = 1) : d115751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12453, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28523 q ha hb
    | true =>
      simp only [d12453, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12454 q = 1) (hb : d115574 q = 1) : d115752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12454, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12454, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12455 q = 1) (hb : d115574 q = 1) : d115753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12455, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12455, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12456 q = 1) (hb : d115574 q = 1) : d115754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12456, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12456, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12457 q = 1) (hb : d115574 q = 1) : d115755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12457, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12457, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12573 q = 1) (hb : d115574 q = 1) : d12573 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12574 q = 1) (hb : d115574 q = 1) : d115822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12574, d115822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12574, d115822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28528 (p : Pattern) (ha : d12473 p = 1) (hb : d115574 p = 1) : d115770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d115574 q = 1) : d115748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12472 q = 1) (hb : d115574 q = 1) : d115769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d115769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d115769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12473 q = 1) (hb : d115574 q = 1) : d115770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12473, d115770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12473, d115770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28529 (p : Pattern) (ha : d12482 p = 1) (hb : d115574 p = 1) : d115777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12480 q = 1) (hb : d115574 q = 1) : d115775 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d115775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d115775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12481 q = 1) (hb : d115574 q = 1) : d115776 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d115776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12481, d115776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12482 q = 1) (hb : d115574 q = 1) : d115777 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12482, d115777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12482, d115777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28530 (p : Pattern) (ha : d12502 p = 1) (hb : d115574 p = 1) : d115783 p = 1 := by
  have h0 (q : Pattern) (ha : d12492 q = 1) (hb : d94753 q = 1) : d12492 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12499 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12500 q = 1) (hb : d115574 q = 1) : d115781 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12500, d115574, d115781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12500, d115574, d115781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d94753 q = 1) : d12315 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4821 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12316 q = 1) (hb : d115574 q = 1) : d115660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12316, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12316, d115574, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d12501 q = 1) (hb : d115574 q = 1) : d115782 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12501, d115782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12501, d115782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12502 q = 1) (hb : d115574 q = 1) : d115783 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12502, d115783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12502, d115783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28531 (p : Pattern) (ha : d12508 p = 1) (hb : d115574 p = 1) : d115789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d115574 q = 1) : d115784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d115784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28530 q ha hb
    | true =>
      simp only [d12503, d115784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d115574 q = 1) : d115785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d115785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d115785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d115574 q = 1) : d115786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d115786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d115786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d115574 q = 1) : d115787 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d115787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d115787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d115574 q = 1) : d115788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d115788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d115788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12508 q = 1) (hb : d115574 q = 1) : d115789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12508, d115789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12508, d115789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28532 (p : Pattern) (ha : d12537 p = 1) (hb : d115574 p = 1) : d115795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d115574 q = 1) : d115792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d115792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d115792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d115574 q = 1) : d115793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d115793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d115793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d115574 q = 1) : d115794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d115794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d115794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12537 q = 1) (hb : d115574 q = 1) : d115795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12537, d115795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12537, d115795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28533 (p : Pattern) (ha : d115319 p = 1) (hb : d115574 p = 1) : d115801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12475 q = 1) (hb : d115574 q = 1) : d12475 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12476 q = 1) (hb : d115574 q = 1) : d115771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d115771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28528 q ha hb
    | true =>
      simp only [d12476, d115771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12477 q = 1) (hb : d115574 q = 1) : d115772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d115772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d115772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12478 q = 1) (hb : d115574 q = 1) : d115773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d115773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12478, d115773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12479 q = 1) (hb : d115574 q = 1) : d115774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d115774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d115774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d115574 q = 1) : d12485 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12486 q = 1) (hb : d115574 q = 1) : d115778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d115778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28529 q ha hb
    | true =>
      simp only [d12486, d115778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12487 q = 1) (hb : d115574 q = 1) : d115779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d115779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d115779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12488 q = 1) (hb : d115574 q = 1) : d115780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d115780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12488, d115780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12509 q = 1) (hb : d115574 q = 1) : d115790 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d115790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28531 q ha hb
    | true =>
      simp only [d12509, d115790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28523 q ha hb
  have h11 (q : Pattern) (ha : d115315 q = 1) (hb : d115574 q = 1) : d115791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d115791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115315, d115791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12538 q = 1) (hb : d115574 q = 1) : d115796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d115796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28532 q ha hb
    | true =>
      simp only [d12538, d115796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12539 q = 1) (hb : d115574 q = 1) : d115797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d115797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12539, d115797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115316 q = 1) (hb : d115574 q = 1) : d115798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d115798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115316, d115798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115317 q = 1) (hb : d115574 q = 1) : d115799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d115799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115317, d115799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115318 q = 1) (hb : d115574 q = 1) : d115800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d115800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115318, d115800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115319 q = 1) (hb : d115574 q = 1) : d115801 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d115801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d115801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28534 (p : Pattern) (ha : d12544 p = 1) (hb : d115574 p = 1) : d115802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12446 q = 1) (hb : d115574 q = 1) : d115748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12446, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12446, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12472 q = 1) (hb : d115574 q = 1) : d115769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12472, d115769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12472, d115769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12544 q = 1) (hb : d115574 q = 1) : d115802 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12544, d115802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12544, d115802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28535 (p : Pattern) (ha : d12550 p = 1) (hb : d115574 p = 1) : d115807 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12444 q = 1) (hb : d115574 q = 1) : d12444 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12445 q = 1) (hb : d115574 q = 1) : d115747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12445, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12480 q = 1) (hb : d115574 q = 1) : d115775 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12480, d115775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12480, d115775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12481 q = 1) (hb : d115574 q = 1) : d115776 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12481, d115776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12481, d115776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12550 q = 1) (hb : d115574 q = 1) : d115807 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12550, d115807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12550, d115807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28536 (p : Pattern) (ha : d12555 p = 1) (hb : d115574 p = 1) : d115811 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12503 q = 1) (hb : d115574 q = 1) : d115784 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12503, d115784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28530 q ha hb
    | true =>
      simp only [d12503, d115784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12504 q = 1) (hb : d115574 q = 1) : d115785 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12504, d115785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12504, d115785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12505 q = 1) (hb : d115574 q = 1) : d115786 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12505, d115786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12505, d115786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12506 q = 1) (hb : d115574 q = 1) : d115787 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12506, d115787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12506, d115787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12507 q = 1) (hb : d115574 q = 1) : d115788 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12507, d115788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12507, d115788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12555 q = 1) (hb : d115574 q = 1) : d115811 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12555, d115811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12555, d115811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28537 (p : Pattern) (ha : d12561 p = 1) (hb : d115574 p = 1) : d115814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12439 q = 1) (hb : d115574 q = 1) : d115663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28522 q ha hb
    | true =>
      simp only [d12439, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12440 q = 1) (hb : d115574 q = 1) : d115664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12440, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12534 q = 1) (hb : d115574 q = 1) : d115792 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12534, d115792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12534, d115792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12535 q = 1) (hb : d115574 q = 1) : d115793 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12535, d115793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12535, d115793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12536 q = 1) (hb : d115574 q = 1) : d115794 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12536, d115794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12536, d115794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12561 q = 1) (hb : d115574 q = 1) : d115814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12561, d115814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12561, d115814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28538 (p : Pattern) (ha : d115324 p = 1) (hb : d115574 p = 1) : d115820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12475 q = 1) (hb : d115574 q = 1) : d12475 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12476 q = 1) (hb : d115574 q = 1) : d115771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12476, d115771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28528 q ha hb
    | true =>
      simp only [d12476, d115771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12477 q = 1) (hb : d115574 q = 1) : d115772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12477, d115772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12477, d115772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12478 q = 1) (hb : d115574 q = 1) : d115773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12478, d115773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12478, d115773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12479 q = 1) (hb : d115574 q = 1) : d115774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12479, d115774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12479, d115774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d115574 q = 1) : d12485 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12486 q = 1) (hb : d115574 q = 1) : d115778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12486, d115778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28529 q ha hb
    | true =>
      simp only [d12486, d115778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12487 q = 1) (hb : d115574 q = 1) : d115779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12487, d115779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12487, d115779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12488 q = 1) (hb : d115574 q = 1) : d115780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12488, d115780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12488, d115780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12509 q = 1) (hb : d115574 q = 1) : d115790 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12509, d115790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28531 q ha hb
    | true =>
      simp only [d12509, d115790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28523 q ha hb
  have h11 (q : Pattern) (ha : d115315 q = 1) (hb : d115574 q = 1) : d115791 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d115791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115315, d115791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12538 q = 1) (hb : d115574 q = 1) : d115796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12538, d115796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28532 q ha hb
    | true =>
      simp only [d12538, d115796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12539 q = 1) (hb : d115574 q = 1) : d115797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12539, d115797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12539, d115797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115316 q = 1) (hb : d115574 q = 1) : d115798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d115798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115316, d115798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115317 q = 1) (hb : d115574 q = 1) : d115799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d115799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115317, d115799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115318 q = 1) (hb : d115574 q = 1) : d115800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d115800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115318, d115800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12545 q = 1) (hb : d115574 q = 1) : d12545 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12546 q = 1) (hb : d115574 q = 1) : d115803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12546, d115803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28534 q ha hb
    | true =>
      simp only [d12546, d115803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12547 q = 1) (hb : d115574 q = 1) : d115804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12547, d115804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12547, d115804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12548 q = 1) (hb : d115574 q = 1) : d115805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12548, d115805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12548, d115805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12549 q = 1) (hb : d115574 q = 1) : d115806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12549, d115806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12549, d115806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12551 q = 1) (hb : d115574 q = 1) : d12551 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12552 q = 1) (hb : d115574 q = 1) : d115808 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12552, d115808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28535 q ha hb
    | true =>
      simp only [d12552, d115808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12553 q = 1) (hb : d115574 q = 1) : d115809 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12553, d115809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12553, d115809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12554 q = 1) (hb : d115574 q = 1) : d115810 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12554, d115810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12554, d115810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12556 q = 1) (hb : d115574 q = 1) : d115812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d115812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28536 q ha hb
    | true =>
      simp only [d12556, d115812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28525 q ha hb
  have h27 (q : Pattern) (ha : d115320 q = 1) (hb : d115574 q = 1) : d115813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d115813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115320, d115813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d12562 q = 1) (hb : d115574 q = 1) : d115815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d115815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28537 q ha hb
    | true =>
      simp only [d12562, d115815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12563 q = 1) (hb : d115574 q = 1) : d115816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d115816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12563, d115816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115321 q = 1) (hb : d115574 q = 1) : d115817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d115817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115321, d115817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115322 q = 1) (hb : d115574 q = 1) : d115818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d115818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115322, d115818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115323 q = 1) (hb : d115574 q = 1) : d115819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d115819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115323, d115819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115324 q = 1) (hb : d115574 q = 1) : d115820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d115820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115324, d115820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro28539 (p : Pattern) (ha : d115331 p = 1) (hb : d115574 p = 1) : d115829 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12556 q = 1) (hb : d115574 q = 1) : d115812 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12556, d115812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28536 q ha hb
    | true =>
      simp only [d12556, d115812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28525 q ha hb
  have h2 (q : Pattern) (ha : d115320 q = 1) (hb : d115574 q = 1) : d115813 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d115813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115320, d115813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12562 q = 1) (hb : d115574 q = 1) : d115815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12562, d115815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28537 q ha hb
    | true =>
      simp only [d12562, d115815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12563 q = 1) (hb : d115574 q = 1) : d115816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12563, d115816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12563, d115816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d115574 q = 1) : d115817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d115817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115321, d115817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d115574 q = 1) : d115827 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d115827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d115827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d115574 q = 1) : d115828 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d115828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d115828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d115574 q = 1) : d115829 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d115829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d115829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28540 (p : Pattern) (ha : d12610 p = 1) (hb : d115574 p = 1) : d115837 p = 1 := by
  have h0 (q : Pattern) (ha : d12598 q = 1) (hb : d94753 q = 1) : d12598 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12607 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12608 q = 1) (hb : d115574 q = 1) : d115835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12608, d115574, d115835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12608, d115574, d115835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d94753 q = 1) : d12389 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6081 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12390 q = 1) (hb : d115574 q = 1) : d115714 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d115574, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12390, d115574, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d12609 q = 1) (hb : d115574 q = 1) : d115836 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12609, d115836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12609, d115836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12610 q = 1) (hb : d115574 q = 1) : d115837 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12610, d115837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12610, d115837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28541 (p : Pattern) (ha : d12614 p = 1) (hb : d115574 p = 1) : d115716 p = 1 := by
  have h0 (q : Pattern) (ha : d12389 q = 1) (hb : d94753 q = 1) : d12389 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12390 q = 1) (hb : d115574 q = 1) : d115714 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12390, d115574, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12390, d115574, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6082 q = 1) (hb : d115574 q = 1) : d6082 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12613 q = 1) (hb : d115574 q = 1) : d115715 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12613, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12613, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12614 q = 1) (hb : d115574 q = 1) : d115716 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12614, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12614, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28542 (p : Pattern) (ha : d12620 p = 1) (hb : d115574 p = 1) : d115843 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12611 q = 1) (hb : d115574 q = 1) : d115838 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12611, d115838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28540 q ha hb
    | true =>
      simp only [d12611, d115838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12612 q = 1) (hb : d115574 q = 1) : d115839 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12612, d115839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12612, d115839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12615 q = 1) (hb : d115574 q = 1) : d115717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28541 q ha hb
    | true =>
      simp only [d12615, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12616 q = 1) (hb : d115574 q = 1) : d115718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12617 q = 1) (hb : d115574 q = 1) : d115840 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12617, d115840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12617, d115840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12618 q = 1) (hb : d115574 q = 1) : d115841 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12618, d115841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12618, d115841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12619 q = 1) (hb : d115574 q = 1) : d115842 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12619, d115842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12619, d115842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12620 q = 1) (hb : d115574 q = 1) : d115843 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12620, d115843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12620, d115843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28543 (p : Pattern) (ha : d12628 p = 1) (hb : d115574 p = 1) : d115847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d115574 q = 1) : d115717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28541 q ha hb
    | true =>
      simp only [d12615, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d115574 q = 1) : d115718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12624 q = 1) (hb : d115574 q = 1) : d12624 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12625 q = 1) (hb : d115574 q = 1) : d115844 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12625, d115844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12625, d115844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12626 q = 1) (hb : d115574 q = 1) : d115845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12626, d115845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12626, d115845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12627 q = 1) (hb : d115574 q = 1) : d115846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12627, d115846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12627, d115846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12628 q = 1) (hb : d115574 q = 1) : d115847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12628, d115847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12628, d115847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28544 (p : Pattern) (ha : d12657 p = 1) (hb : d115574 p = 1) : d115853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12615 q = 1) (hb : d115574 q = 1) : d115717 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12615, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28541 q ha hb
    | true =>
      simp only [d12615, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12616 q = 1) (hb : d115574 q = 1) : d115718 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12616, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12616, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12654 q = 1) (hb : d115574 q = 1) : d115850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12654, d115850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12654, d115850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12655 q = 1) (hb : d115574 q = 1) : d115851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12655, d115851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12655, d115851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12656 q = 1) (hb : d115574 q = 1) : d115852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12656, d115852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12656, d115852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12657 q = 1) (hb : d115574 q = 1) : d115853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12657, d115853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12657, d115853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28545 (p : Pattern) (ha : d115341 p = 1) (hb : d115574 p = 1) : d115859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12629 q = 1) (hb : d115574 q = 1) : d115848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12629, d115848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28542 q ha hb
    | true =>
      simp only [d12629, d115848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28543 q ha hb
  have h2 (q : Pattern) (ha : d115337 q = 1) (hb : d115574 q = 1) : d115849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d115849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115337, d115849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12658 q = 1) (hb : d115574 q = 1) : d115854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12658, d115854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28544 q ha hb
    | true =>
      simp only [d12658, d115854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12659 q = 1) (hb : d115574 q = 1) : d115855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12659, d115855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12659, d115855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d115574 q = 1) : d115856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d115856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115338, d115856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d115574 q = 1) : d115857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d115857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d115857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d115574 q = 1) : d115858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d115858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d115858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d115574 q = 1) : d115859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d115859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d115859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28546 (p : Pattern) (ha : d115347 p = 1) (hb : d115574 p = 1) : d115865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12459 q = 1) (hb : d115574 q = 1) : d115757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12459, d115757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12459, d115757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28524 q ha hb
  have h2 (q : Pattern) (ha : d12460 q = 1) (hb : d115574 q = 1) : d115758 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12460, d115758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12460, d115758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12469 q = 1) (hb : d115574 q = 1) : d115766 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d115766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28524 q ha hb
    | true =>
      simp only [d12469, d115766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28526 q ha hb
  have h4 (q : Pattern) (ha : d12470 q = 1) (hb : d115574 q = 1) : d115767 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d115767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12470, d115767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12471 q = 1) (hb : d115574 q = 1) : d115768 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12471, d115768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12471, d115768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115325 q = 1) (hb : d115574 q = 1) : d115821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d115821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28533 q ha hb
    | true =>
      simp only [d115325, d115821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28538 q ha hb
  have h7 (q : Pattern) (ha : d12580 q = 1) (hb : d115574 q = 1) : d12580 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12581 q = 1) (hb : d115574 q = 1) : d115823 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12581, d115823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28527 q ha hb
    | true =>
      simp only [d12581, d115823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115326 q = 1) (hb : d115574 q = 1) : d115824 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d115824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115326, d115824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115327 q = 1) (hb : d115574 q = 1) : d115825 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d115825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115327, d115825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115328 q = 1) (hb : d115574 q = 1) : d115826 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d115826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115328, d115826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115332 q = 1) (hb : d115574 q = 1) : d115830 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d115830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115332, d115830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28539 q ha hb
  have h13 (q : Pattern) (ha : d12590 q = 1) (hb : d115574 q = 1) : d12590 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115333 q = 1) (hb : d115574 q = 1) : d115831 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d115831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115333, d115831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115334 q = 1) (hb : d115574 q = 1) : d115832 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d115832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115334, d115832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115335 q = 1) (hb : d115574 q = 1) : d115833 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d115833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115335, d115833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115336 q = 1) (hb : d115574 q = 1) : d115834 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d115834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115336, d115834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115342 q = 1) (hb : d115574 q = 1) : d115860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d115860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115342, d115860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28545 q ha hb
  have h19 (q : Pattern) (ha : d12675 q = 1) (hb : d115574 q = 1) : d12675 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115343 q = 1) (hb : d115574 q = 1) : d115861 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d115861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115343, d115861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115344 q = 1) (hb : d115574 q = 1) : d115862 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d115862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115344, d115862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115345 q = 1) (hb : d115574 q = 1) : d115863 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d115863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115345, d115863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115346 q = 1) (hb : d115574 q = 1) : d115864 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d115864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115346, d115864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115347 q = 1) (hb : d115574 q = 1) : d115865 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d115865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115347, d115865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro28547 (p : Pattern) (ha : d115353 p = 1) (hb : d115574 p = 1) : d115871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d115574 q = 1) : d115866 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d115866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d115866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28546 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d115574 q = 1) : d115867 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d115867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d115867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d115574 q = 1) : d115868 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d115868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d115868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d115574 q = 1) : d115869 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d115869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d115869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d115574 q = 1) : d115870 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d115870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d115870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d115574 q = 1) : d115871 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d115871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d115871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28548 (p : Pattern) (ha : d12693 p = 1) (hb : d115574 p = 1) : d115875 p = 1 := by
  have h0 (q : Pattern) (ha : d12690 q = 1) (hb : d94753 q = 1) : d12690 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d4916 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12691 q = 1) (hb : d115574 q = 1) : d115873 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d115574, d115873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12691, d115574, d115873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d4917 q = 1) (hb : d115574 q = 1) : d4917 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12692 q = 1) (hb : d115574 q = 1) : d115874 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12692, d115874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12692, d115874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12693 q = 1) (hb : d115574 q = 1) : d115875 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12693, d115875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12693, d115875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28549 (p : Pattern) (ha : d12703 p = 1) (hb : d115574 p = 1) : d115881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d115574 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d115574 q = 1) : d115878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d115574 q = 1) : d115879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d115879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d115879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12702 q = 1) (hb : d115574 q = 1) : d115880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d115880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12702, d115880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12703 q = 1) (hb : d115574 q = 1) : d115881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12703, d115881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12703, d115881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28550 (p : Pattern) (ha : d12713 p = 1) (hb : d115574 p = 1) : d115887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d115574 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d115574 q = 1) : d115882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d115882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28549 q ha hb
    | true =>
      simp only [d12708, d115882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d115574 q = 1) : d115883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d115574 q = 1) : d115884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d115574 q = 1) : d115885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d115574 q = 1) : d115886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12713 q = 1) (hb : d115574 q = 1) : d115887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12713, d115887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12713, d115887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28551 (p : Pattern) (ha : d12716 p = 1) (hb : d115574 p = 1) : d115890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d115574 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d115574 q = 1) : d115878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d115574 q = 1) : d115879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d115879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d115879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12702 q = 1) (hb : d115574 q = 1) : d115880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12702, d115880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12702, d115880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12716 q = 1) (hb : d115574 q = 1) : d115890 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12716, d115890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12716, d115890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28552 (p : Pattern) (ha : d12723 p = 1) (hb : d115574 p = 1) : d115896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d115574 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d115574 q = 1) : d115882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d115882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28549 q ha hb
    | true =>
      simp only [d12708, d115882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d115574 q = 1) : d115883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d115574 q = 1) : d115884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d115574 q = 1) : d115885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d115574 q = 1) : d115886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12717 q = 1) (hb : d115574 q = 1) : d12717 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12718 q = 1) (hb : d115574 q = 1) : d115891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d115891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28551 q ha hb
    | true =>
      simp only [d12718, d115891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12719 q = 1) (hb : d115574 q = 1) : d115892 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d115892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d115892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12720 q = 1) (hb : d115574 q = 1) : d115893 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d115893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12720, d115893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12721 q = 1) (hb : d115574 q = 1) : d115894 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d115894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d115894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12722 q = 1) (hb : d115574 q = 1) : d115895 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d115895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d115895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12723 q = 1) (hb : d115574 q = 1) : d115896 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12723, d115896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12723, d115896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro28553 (p : Pattern) (ha : d12833 p = 1) (hb : d115574 p = 1) : d115953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12707 q = 1) (hb : d115574 q = 1) : d12707 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12708 q = 1) (hb : d115574 q = 1) : d115882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12708, d115882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28549 q ha hb
    | true =>
      simp only [d12708, d115882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12709 q = 1) (hb : d115574 q = 1) : d115883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12709, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12709, d115883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12710 q = 1) (hb : d115574 q = 1) : d115884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12710, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12710, d115884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12711 q = 1) (hb : d115574 q = 1) : d115885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12711, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12711, d115885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12712 q = 1) (hb : d115574 q = 1) : d115886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12712, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12712, d115886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12832 q = 1) (hb : d115574 q = 1) : d12832 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12833 q = 1) (hb : d115574 q = 1) : d115953 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12833, d115953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12833, d115953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28554 (p : Pattern) (ha : d12728 p = 1) (hb : d115574 p = 1) : d115901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d115574 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d115574 q = 1) : d115878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d115574 q = 1) : d115879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d115879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d115879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12727 q = 1) (hb : d115574 q = 1) : d115900 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d115900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d115900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12728 q = 1) (hb : d115574 q = 1) : d115901 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12728, d115901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12728, d115901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28555 (p : Pattern) (ha : d12737 p = 1) (hb : d115574 p = 1) : d115908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d115574 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d115574 q = 1) : d115878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12735 q = 1) (hb : d115574 q = 1) : d115906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d115906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d115906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12736 q = 1) (hb : d115574 q = 1) : d115907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d115907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12736, d115907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12737 q = 1) (hb : d115574 q = 1) : d115908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12737, d115908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12737, d115908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28556 (p : Pattern) (ha : d12757 p = 1) (hb : d115574 p = 1) : d115914 p = 1 := by
  have h0 (q : Pattern) (ha : d12747 q = 1) (hb : d94753 q = 1) : d12747 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12755 q = 1) (hb : d115574 q = 1) : d115912 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12755, d115574, d115912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12755, d115574, d115912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12690 q = 1) (hb : d94753 q = 1) : d12690 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d4916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12691 q = 1) (hb : d115574 q = 1) : d115873 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12691, d115574, d115873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12691, d115574, d115873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d12756 q = 1) (hb : d115574 q = 1) : d115913 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12756, d115913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12756, d115913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12757 q = 1) (hb : d115574 q = 1) : d115914 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12757, d115914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12757, d115914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28557 (p : Pattern) (ha : d12763 p = 1) (hb : d115574 p = 1) : d115920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d115574 q = 1) : d115915 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d115915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28556 q ha hb
    | true =>
      simp only [d12758, d115915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d115574 q = 1) : d115916 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d115916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d115916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d115574 q = 1) : d115917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d115917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d115917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d115574 q = 1) : d115918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d115918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d115918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d115574 q = 1) : d115919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d115919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d115919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12763 q = 1) (hb : d115574 q = 1) : d115920 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12763, d115920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12763, d115920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28558 (p : Pattern) (ha : d12796 p = 1) (hb : d115574 p = 1) : d115926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d115574 q = 1) : d115923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d115923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d115923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d115574 q = 1) : d115924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d115924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d115924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d115574 q = 1) : d115925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d115925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d115925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12796 q = 1) (hb : d115574 q = 1) : d115926 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12796, d115926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12796, d115926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28559 (p : Pattern) (ha : d115359 p = 1) (hb : d115574 p = 1) : d115932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12730 q = 1) (hb : d115574 q = 1) : d12730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12731 q = 1) (hb : d115574 q = 1) : d115902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d115902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28554 q ha hb
    | true =>
      simp only [d12731, d115902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12732 q = 1) (hb : d115574 q = 1) : d115903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d115903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d115903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12733 q = 1) (hb : d115574 q = 1) : d115904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d115904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12733, d115904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12734 q = 1) (hb : d115574 q = 1) : d115905 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d115905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d115905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d115574 q = 1) : d12740 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12741 q = 1) (hb : d115574 q = 1) : d115909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d115909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28555 q ha hb
    | true =>
      simp only [d12741, d115909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12742 q = 1) (hb : d115574 q = 1) : d115910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d115910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d115910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12743 q = 1) (hb : d115574 q = 1) : d115911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d115911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12743, d115911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12764 q = 1) (hb : d115574 q = 1) : d115921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d115921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28557 q ha hb
    | true =>
      simp only [d12764, d115921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28549 q ha hb
  have h11 (q : Pattern) (ha : d115355 q = 1) (hb : d115574 q = 1) : d115922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d115922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115355, d115922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12797 q = 1) (hb : d115574 q = 1) : d115927 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d115927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28558 q ha hb
    | true =>
      simp only [d12797, d115927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12798 q = 1) (hb : d115574 q = 1) : d115928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d115928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12798, d115928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115356 q = 1) (hb : d115574 q = 1) : d115929 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d115929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115356, d115929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115357 q = 1) (hb : d115574 q = 1) : d115930 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d115930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115357, d115930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115358 q = 1) (hb : d115574 q = 1) : d115931 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d115931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115358, d115931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115359 q = 1) (hb : d115574 q = 1) : d115932 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d115932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d115932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28560 (p : Pattern) (ha : d12803 p = 1) (hb : d115574 p = 1) : d115933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d115574 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d115574 q = 1) : d115878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12701 q = 1) (hb : d115574 q = 1) : d115879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12701, d115879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12701, d115879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12727 q = 1) (hb : d115574 q = 1) : d115900 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12727, d115900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12727, d115900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12803 q = 1) (hb : d115574 q = 1) : d115933 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12803, d115933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12803, d115933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28561 (p : Pattern) (ha : d12809 p = 1) (hb : d115574 p = 1) : d115938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12699 q = 1) (hb : d115574 q = 1) : d12699 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12700 q = 1) (hb : d115574 q = 1) : d115878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12700, d115878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12735 q = 1) (hb : d115574 q = 1) : d115906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12735, d115906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12735, d115906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12736 q = 1) (hb : d115574 q = 1) : d115907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12736, d115907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12736, d115907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12809 q = 1) (hb : d115574 q = 1) : d115938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12809, d115938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12809, d115938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28562 (p : Pattern) (ha : d12814 p = 1) (hb : d115574 p = 1) : d115942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12758 q = 1) (hb : d115574 q = 1) : d115915 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12758, d115915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28556 q ha hb
    | true =>
      simp only [d12758, d115915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12759 q = 1) (hb : d115574 q = 1) : d115916 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12759, d115916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12759, d115916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12760 q = 1) (hb : d115574 q = 1) : d115917 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12760, d115917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12760, d115917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12761 q = 1) (hb : d115574 q = 1) : d115918 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12761, d115918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12761, d115918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12762 q = 1) (hb : d115574 q = 1) : d115919 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12762, d115919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12762, d115919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12814 q = 1) (hb : d115574 q = 1) : d115942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12814, d115942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12814, d115942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28563 (p : Pattern) (ha : d12820 p = 1) (hb : d115574 p = 1) : d115945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12694 q = 1) (hb : d115574 q = 1) : d115876 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28548 q ha hb
    | true =>
      simp only [d12694, d115876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12695 q = 1) (hb : d115574 q = 1) : d115877 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12695, d115877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12793 q = 1) (hb : d115574 q = 1) : d115923 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12793, d115923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12793, d115923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12794 q = 1) (hb : d115574 q = 1) : d115924 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12794, d115924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12794, d115924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12795 q = 1) (hb : d115574 q = 1) : d115925 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12795, d115925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12795, d115925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12820 q = 1) (hb : d115574 q = 1) : d115945 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12820, d115945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12820, d115945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28564 (p : Pattern) (ha : d115364 p = 1) (hb : d115574 p = 1) : d115951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12730 q = 1) (hb : d115574 q = 1) : d12730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12731 q = 1) (hb : d115574 q = 1) : d115902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12731, d115902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28554 q ha hb
    | true =>
      simp only [d12731, d115902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12732 q = 1) (hb : d115574 q = 1) : d115903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12732, d115903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12732, d115903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12733 q = 1) (hb : d115574 q = 1) : d115904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12733, d115904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12733, d115904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12734 q = 1) (hb : d115574 q = 1) : d115905 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12734, d115905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12734, d115905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12740 q = 1) (hb : d115574 q = 1) : d12740 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12741 q = 1) (hb : d115574 q = 1) : d115909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12741, d115909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28555 q ha hb
    | true =>
      simp only [d12741, d115909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12742 q = 1) (hb : d115574 q = 1) : d115910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12742, d115910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12742, d115910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12743 q = 1) (hb : d115574 q = 1) : d115911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12743, d115911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d12743, d115911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d12764 q = 1) (hb : d115574 q = 1) : d115921 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12764, d115921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28557 q ha hb
    | true =>
      simp only [d12764, d115921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28549 q ha hb
  have h11 (q : Pattern) (ha : d115355 q = 1) (hb : d115574 q = 1) : d115922 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d115922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115355, d115922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12797 q = 1) (hb : d115574 q = 1) : d115927 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12797, d115927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28558 q ha hb
    | true =>
      simp only [d12797, d115927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12798 q = 1) (hb : d115574 q = 1) : d115928 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12798, d115928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12798, d115928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115356 q = 1) (hb : d115574 q = 1) : d115929 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d115929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115356, d115929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115357 q = 1) (hb : d115574 q = 1) : d115930 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d115930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115357, d115930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115358 q = 1) (hb : d115574 q = 1) : d115931 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d115931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115358, d115931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12804 q = 1) (hb : d115574 q = 1) : d12804 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d12805 q = 1) (hb : d115574 q = 1) : d115934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12805, d115934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28560 q ha hb
    | true =>
      simp only [d12805, d115934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12806 q = 1) (hb : d115574 q = 1) : d115935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12806, d115935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12806, d115935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d12807 q = 1) (hb : d115574 q = 1) : d115936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12807, d115936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12807, d115936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d12808 q = 1) (hb : d115574 q = 1) : d115937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12808, d115937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12808, d115937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d12810 q = 1) (hb : d115574 q = 1) : d12810 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12811 q = 1) (hb : d115574 q = 1) : d115939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12811, d115939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28561 q ha hb
    | true =>
      simp only [d12811, d115939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d12812 q = 1) (hb : d115574 q = 1) : d115940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12812, d115940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12812, d115940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12813 q = 1) (hb : d115574 q = 1) : d115941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12813, d115941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12813, d115941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12815 q = 1) (hb : d115574 q = 1) : d115943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d115943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28562 q ha hb
    | true =>
      simp only [d12815, d115943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28551 q ha hb
  have h27 (q : Pattern) (ha : d115360 q = 1) (hb : d115574 q = 1) : d115944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d115944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115360, d115944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d12821 q = 1) (hb : d115574 q = 1) : d115946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d115946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28563 q ha hb
    | true =>
      simp only [d12821, d115946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d12822 q = 1) (hb : d115574 q = 1) : d115947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d115947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d12822, d115947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115361 q = 1) (hb : d115574 q = 1) : d115948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d115948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115361, d115948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115362 q = 1) (hb : d115574 q = 1) : d115949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d115949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115362, d115949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115363 q = 1) (hb : d115574 q = 1) : d115950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d115950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115363, d115950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115364 q = 1) (hb : d115574 q = 1) : d115951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d115951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115364, d115951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro28565 (p : Pattern) (ha : d115371 p = 1) (hb : d115574 p = 1) : d115960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12815 q = 1) (hb : d115574 q = 1) : d115943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12815, d115943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28562 q ha hb
    | true =>
      simp only [d12815, d115943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28551 q ha hb
  have h2 (q : Pattern) (ha : d115360 q = 1) (hb : d115574 q = 1) : d115944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d115944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115360, d115944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12821 q = 1) (hb : d115574 q = 1) : d115946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12821, d115946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28563 q ha hb
    | true =>
      simp only [d12821, d115946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12822 q = 1) (hb : d115574 q = 1) : d115947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12822, d115947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12822, d115947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d115574 q = 1) : d115948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d115948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115361, d115948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d115574 q = 1) : d115958 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d115958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d115958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d115574 q = 1) : d115959 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d115959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d115959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d115574 q = 1) : d115960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d115960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d115960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28566 (p : Pattern) (ha : d12873 p = 1) (hb : d115574 p = 1) : d115969 p = 1 := by
  have h0 (q : Pattern) (ha : d12857 q = 1) (hb : d94753 q = 1) : d12857 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12867 q = 1) (hb : d115574 q = 1) : d115966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12867, d115574, d115966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12867, d115574, d115966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12870 q = 1) (hb : d94753 q = 1) : d12870 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6213 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12871 q = 1) (hb : d115574 q = 1) : d115967 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d115574, d115967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12871, d115574, d115967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d12872 q = 1) (hb : d115574 q = 1) : d115968 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12872, d115968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12872, d115968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12873 q = 1) (hb : d115574 q = 1) : d115969 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12873, d115969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12873, d115969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28567 (p : Pattern) (ha : d12877 p = 1) (hb : d115574 p = 1) : d115973 p = 1 := by
  have h0 (q : Pattern) (ha : d12870 q = 1) (hb : d94753 q = 1) : d12870 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12871 q = 1) (hb : d115574 q = 1) : d115967 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12871, d115574, d115967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12871, d115574, d115967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6214 q = 1) (hb : d115574 q = 1) : d6214 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12876 q = 1) (hb : d115574 q = 1) : d115972 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12876, d115972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12876, d115972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12877 q = 1) (hb : d115574 q = 1) : d115973 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12877, d115973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12877, d115973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28568 (p : Pattern) (ha : d12883 p = 1) (hb : d115574 p = 1) : d115979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12874 q = 1) (hb : d115574 q = 1) : d115970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12874, d115970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28566 q ha hb
    | true =>
      simp only [d12874, d115970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12875 q = 1) (hb : d115574 q = 1) : d115971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12875, d115971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12875, d115971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12878 q = 1) (hb : d115574 q = 1) : d115974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d115974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28567 q ha hb
    | true =>
      simp only [d12878, d115974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12879 q = 1) (hb : d115574 q = 1) : d115975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d115975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d115975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12880 q = 1) (hb : d115574 q = 1) : d115976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12880, d115976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12880, d115976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12881 q = 1) (hb : d115574 q = 1) : d115977 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12881, d115977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12881, d115977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12882 q = 1) (hb : d115574 q = 1) : d115978 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12882, d115978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12882, d115978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d12883 q = 1) (hb : d115574 q = 1) : d115979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12883, d115979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12883, d115979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28569 (p : Pattern) (ha : d12891 p = 1) (hb : d115574 p = 1) : d115983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d115574 q = 1) : d115974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d115974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28567 q ha hb
    | true =>
      simp only [d12878, d115974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d115574 q = 1) : d115975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d115975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d115975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12887 q = 1) (hb : d115574 q = 1) : d12887 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12888 q = 1) (hb : d115574 q = 1) : d115980 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12888, d115980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12888, d115980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12889 q = 1) (hb : d115574 q = 1) : d115981 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12889, d115981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12889, d115981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12890 q = 1) (hb : d115574 q = 1) : d115982 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12890, d115982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12890, d115982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12891 q = 1) (hb : d115574 q = 1) : d115983 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12891, d115983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12891, d115983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28570 (p : Pattern) (ha : d12924 p = 1) (hb : d115574 p = 1) : d115989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12878 q = 1) (hb : d115574 q = 1) : d115974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12878, d115974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28567 q ha hb
    | true =>
      simp only [d12878, d115974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12879 q = 1) (hb : d115574 q = 1) : d115975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12879, d115975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12879, d115975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12921 q = 1) (hb : d115574 q = 1) : d115986 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12921, d115986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12921, d115986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12922 q = 1) (hb : d115574 q = 1) : d115987 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12922, d115987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12922, d115987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12923 q = 1) (hb : d115574 q = 1) : d115988 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12923, d115988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12923, d115988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12924 q = 1) (hb : d115574 q = 1) : d115989 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12924, d115989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12924, d115989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28571 (p : Pattern) (ha : d115381 p = 1) (hb : d115574 p = 1) : d115995 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12892 q = 1) (hb : d115574 q = 1) : d115984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12892, d115984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28568 q ha hb
    | true =>
      simp only [d12892, d115984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28569 q ha hb
  have h2 (q : Pattern) (ha : d115377 q = 1) (hb : d115574 q = 1) : d115985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d115985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115377, d115985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12925 q = 1) (hb : d115574 q = 1) : d115990 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12925, d115990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28570 q ha hb
    | true =>
      simp only [d12925, d115990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12926 q = 1) (hb : d115574 q = 1) : d115991 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12926, d115991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12926, d115991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d115574 q = 1) : d115992 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d115992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115378, d115992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d115574 q = 1) : d115993 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d115993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d115993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d115574 q = 1) : d115994 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d115994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d115994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d115574 q = 1) : d115995 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d115995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d115995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28572 (p : Pattern) (ha : d115387 p = 1) (hb : d115574 p = 1) : d116001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12714 q = 1) (hb : d115574 q = 1) : d115888 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12714, d115888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12714, d115888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28550 q ha hb
  have h2 (q : Pattern) (ha : d12715 q = 1) (hb : d115574 q = 1) : d115889 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12715, d115889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12715, d115889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12724 q = 1) (hb : d115574 q = 1) : d115897 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d115897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28550 q ha hb
    | true =>
      simp only [d12724, d115897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28552 q ha hb
  have h4 (q : Pattern) (ha : d12725 q = 1) (hb : d115574 q = 1) : d115898 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d115898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12725, d115898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12726 q = 1) (hb : d115574 q = 1) : d115899 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12726, d115899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12726, d115899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115365 q = 1) (hb : d115574 q = 1) : d115952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d115952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28559 q ha hb
    | true =>
      simp only [d115365, d115952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28564 q ha hb
  have h7 (q : Pattern) (ha : d12839 q = 1) (hb : d115574 q = 1) : d12839 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12840 q = 1) (hb : d115574 q = 1) : d115954 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12840, d115954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28553 q ha hb
    | true =>
      simp only [d12840, d115954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115366 q = 1) (hb : d115574 q = 1) : d115955 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d115955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115366, d115955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115367 q = 1) (hb : d115574 q = 1) : d115956 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d115956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115367, d115956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115368 q = 1) (hb : d115574 q = 1) : d115957 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d115957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115368, d115957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115372 q = 1) (hb : d115574 q = 1) : d115961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d115961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115372, d115961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28565 q ha hb
  have h13 (q : Pattern) (ha : d12849 q = 1) (hb : d115574 q = 1) : d12849 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115373 q = 1) (hb : d115574 q = 1) : d115962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d115962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115373, d115962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115374 q = 1) (hb : d115574 q = 1) : d115963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d115963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115374, d115963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115375 q = 1) (hb : d115574 q = 1) : d115964 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d115964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115375, d115964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115376 q = 1) (hb : d115574 q = 1) : d115965 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d115965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115376, d115965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115382 q = 1) (hb : d115574 q = 1) : d115996 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d115996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115382, d115996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28571 q ha hb
  have h19 (q : Pattern) (ha : d12942 q = 1) (hb : d115574 q = 1) : d12942 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115383 q = 1) (hb : d115574 q = 1) : d115997 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d115997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115383, d115997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115384 q = 1) (hb : d115574 q = 1) : d115998 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d115998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115384, d115998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115385 q = 1) (hb : d115574 q = 1) : d115999 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d115999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115385, d115999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115386 q = 1) (hb : d115574 q = 1) : d116000 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d116000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115386, d116000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115387 q = 1) (hb : d115574 q = 1) : d116001 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d116001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115387, d116001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro28573 (p : Pattern) (ha : d115393 p = 1) (hb : d115574 p = 1) : d116007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d115574 q = 1) : d116002 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d116002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d116002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28572 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d115574 q = 1) : d116003 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d116003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d116003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d115574 q = 1) : d116004 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d116004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d116004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d115574 q = 1) : d116005 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d116005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d116005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d115574 q = 1) : d116006 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d116006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d116006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d115574 q = 1) : d116007 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d116007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d116007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28574 (p : Pattern) (ha : d12967 p = 1) (hb : d115574 p = 1) : d116012 p = 1 := by
  have h0 (q : Pattern) (ha : d12959 q = 1) (hb : d94753 q = 1) : d12959 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12960 q = 1) (hb : d115574 q = 1) : d116010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d115574, d116010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12960, d115574, d116010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12965 q = 1) (hb : d115574 q = 1) : d12965 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12966 q = 1) (hb : d115574 q = 1) : d116011 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12966, d116011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12966, d116011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12967 q = 1) (hb : d115574 q = 1) : d116012 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12967, d116012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12967, d116012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28575 (p : Pattern) (ha : d12977 p = 1) (hb : d115574 p = 1) : d116018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d115574 q = 1) : d116013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28574 q ha hb
    | true =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d115574 q = 1) : d116014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d115574 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d115574 q = 1) : d116015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12975 q = 1) (hb : d115574 q = 1) : d116016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d116016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12975, d116016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12976 q = 1) (hb : d115574 q = 1) : d116017 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d116017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12976, d116017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12977 q = 1) (hb : d115574 q = 1) : d116018 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12977, d116018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12977, d116018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28576 (p : Pattern) (ha : d12987 p = 1) (hb : d115574 p = 1) : d116024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12981 q = 1) (hb : d115574 q = 1) : d12981 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12982 q = 1) (hb : d115574 q = 1) : d116019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d116019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28575 q ha hb
    | true =>
      simp only [d12982, d116019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12983 q = 1) (hb : d115574 q = 1) : d116020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d116020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d116020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12984 q = 1) (hb : d115574 q = 1) : d116021 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d116021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12984, d116021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12985 q = 1) (hb : d115574 q = 1) : d116022 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d116022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d116022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12986 q = 1) (hb : d115574 q = 1) : d116023 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d116023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d116023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12987 q = 1) (hb : d115574 q = 1) : d116024 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12987, d116024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12987, d116024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28577 (p : Pattern) (ha : d12990 p = 1) (hb : d115574 p = 1) : d116027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d115574 q = 1) : d116013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28574 q ha hb
    | true =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d115574 q = 1) : d116014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d115574 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d115574 q = 1) : d116015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12975 q = 1) (hb : d115574 q = 1) : d116016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d116016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12975, d116016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12976 q = 1) (hb : d115574 q = 1) : d116017 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12976, d116017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12976, d116017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12990 q = 1) (hb : d115574 q = 1) : d116027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12990, d116027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12990, d116027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28578 (p : Pattern) (ha : d12997 p = 1) (hb : d115574 p = 1) : d116033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12981 q = 1) (hb : d115574 q = 1) : d12981 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12982 q = 1) (hb : d115574 q = 1) : d116019 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12982, d116019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28575 q ha hb
    | true =>
      simp only [d12982, d116019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12983 q = 1) (hb : d115574 q = 1) : d116020 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12983, d116020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12983, d116020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12984 q = 1) (hb : d115574 q = 1) : d116021 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12984, d116021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12984, d116021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12985 q = 1) (hb : d115574 q = 1) : d116022 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12985, d116022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12985, d116022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12986 q = 1) (hb : d115574 q = 1) : d116023 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12986, d116023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12986, d116023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12991 q = 1) (hb : d115574 q = 1) : d12991 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12992 q = 1) (hb : d115574 q = 1) : d116028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d116028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28577 q ha hb
    | true =>
      simp only [d12992, d116028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12993 q = 1) (hb : d115574 q = 1) : d116029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d116029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d116029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12994 q = 1) (hb : d115574 q = 1) : d116030 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d116030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12994, d116030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d12995 q = 1) (hb : d115574 q = 1) : d116031 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d116031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d116031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d12996 q = 1) (hb : d115574 q = 1) : d116032 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d116032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d116032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12997 q = 1) (hb : d115574 q = 1) : d116033 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12997, d116033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12997, d116033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro28579 (p : Pattern) (ha : d13040 p = 1) (hb : d115574 p = 1) : d116055 p = 1 := by
  have h0 (q : Pattern) (ha : d12959 q = 1) (hb : d94753 q = 1) : d12959 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12960 q = 1) (hb : d115574 q = 1) : d116010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d115574, d116010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12960, d115574, d116010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5027 q = 1) (hb : d115574 q = 1) : d5027 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13039 q = 1) (hb : d115574 q = 1) : d116054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13039, d116054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13039, d116054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13040 q = 1) (hb : d115574 q = 1) : d116055 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13040, d116055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13040, d116055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28580 (p : Pattern) (ha : d13050 p = 1) (hb : d115574 p = 1) : d116065 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d115574 q = 1) : d116056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d116056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28579 q ha hb
    | true =>
      simp only [d13041, d116056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d115574 q = 1) : d116057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d116057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d116057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d115574 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13047 q = 1) (hb : d115574 q = 1) : d116062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d116062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d116062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13048 q = 1) (hb : d115574 q = 1) : d116063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d116063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13048, d116063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13049 q = 1) (hb : d115574 q = 1) : d116064 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d116064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13049, d116064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13050 q = 1) (hb : d115574 q = 1) : d116065 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13050, d116065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13050, d116065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28581 (p : Pattern) (ha : d13134 p = 1) (hb : d115574 p = 1) : d116104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12981 q = 1) (hb : d115574 q = 1) : d12981 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13124 q = 1) (hb : d115574 q = 1) : d116099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13124, d116099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28580 q ha hb
    | true =>
      simp only [d13124, d116099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13125 q = 1) (hb : d115574 q = 1) : d116100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13125, d116100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13125, d116100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13126 q = 1) (hb : d115574 q = 1) : d116101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13126, d116101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13126, d116101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13127 q = 1) (hb : d115574 q = 1) : d116102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13127, d116102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13127, d116102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13128 q = 1) (hb : d115574 q = 1) : d116103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13128, d116103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13128, d116103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13133 q = 1) (hb : d115574 q = 1) : d13133 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13134 q = 1) (hb : d115574 q = 1) : d116104 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13134, d116104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13134, d116104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28582 (p : Pattern) (ha : d13002 p = 1) (hb : d115574 p = 1) : d116038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d115574 q = 1) : d116013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28574 q ha hb
    | true =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d115574 q = 1) : d116014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d115574 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d115574 q = 1) : d116015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12975 q = 1) (hb : d115574 q = 1) : d116016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d116016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12975, d116016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13001 q = 1) (hb : d115574 q = 1) : d116037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d116037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d116037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13002 q = 1) (hb : d115574 q = 1) : d116038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13002, d116038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13002, d116038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28583 (p : Pattern) (ha : d13011 p = 1) (hb : d115574 p = 1) : d116045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d115574 q = 1) : d116013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28574 q ha hb
    | true =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d115574 q = 1) : d116014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d115574 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d115574 q = 1) : d116015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13009 q = 1) (hb : d115574 q = 1) : d116043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d116043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d116043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13010 q = 1) (hb : d115574 q = 1) : d116044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d116044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13010, d116044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13011 q = 1) (hb : d115574 q = 1) : d116045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13011, d116045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13011, d116045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28584 (p : Pattern) (ha : d13036 p = 1) (hb : d115574 p = 1) : d116051 p = 1 := by
  have h0 (q : Pattern) (ha : d13021 q = 1) (hb : d94753 q = 1) : d13021 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13033 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13034 q = 1) (hb : d115574 q = 1) : d116049 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13034, d115574, d116049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13034, d115574, d116049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d12959 q = 1) (hb : d94753 q = 1) : d12959 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d12960 q = 1) (hb : d115574 q = 1) : d116010 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12960, d115574, d116010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12960, d115574, d116010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13035 q = 1) (hb : d115574 q = 1) : d116050 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13035, d116050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13035, d116050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13036 q = 1) (hb : d115574 q = 1) : d116051 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13036, d116051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13036, d116051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28585 (p : Pattern) (ha : d13046 p = 1) (hb : d115574 p = 1) : d116061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d115574 q = 1) : d116052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d116052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28584 q ha hb
    | true =>
      simp only [d13037, d116052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d115574 q = 1) : d116053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d116053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d116053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d115574 q = 1) : d116056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d116056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28579 q ha hb
    | true =>
      simp only [d13041, d116056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d115574 q = 1) : d116057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d116057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d116057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d115574 q = 1) : d116058 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d116058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d116058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d115574 q = 1) : d116059 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d116059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d116059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d115574 q = 1) : d116060 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d116060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d116060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13046 q = 1) (hb : d115574 q = 1) : d116061 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13046, d116061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13046, d116061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28586 (p : Pattern) (ha : d13091 p = 1) (hb : d115574 p = 1) : d116071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d115574 q = 1) : d116013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28574 q ha hb
    | true =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d115574 q = 1) : d116014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d115574 q = 1) : d116068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d116068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d116068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d115574 q = 1) : d116069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d116069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d116069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d115574 q = 1) : d116070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d116070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d116070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13091 q = 1) (hb : d115574 q = 1) : d116071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13091, d116071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13091, d116071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28587 (p : Pattern) (ha : d115400 p = 1) (hb : d115574 p = 1) : d116077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13004 q = 1) (hb : d115574 q = 1) : d13004 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13005 q = 1) (hb : d115574 q = 1) : d116039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d116039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28582 q ha hb
    | true =>
      simp only [d13005, d116039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13006 q = 1) (hb : d115574 q = 1) : d116040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d116040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d116040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13007 q = 1) (hb : d115574 q = 1) : d116041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d116041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13007, d116041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13008 q = 1) (hb : d115574 q = 1) : d116042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d116042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d116042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d115574 q = 1) : d13014 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13015 q = 1) (hb : d115574 q = 1) : d116046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d116046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28583 q ha hb
    | true =>
      simp only [d13015, d116046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13016 q = 1) (hb : d115574 q = 1) : d116047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d116047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d116047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13017 q = 1) (hb : d115574 q = 1) : d116048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d116048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13017, d116048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13051 q = 1) (hb : d115574 q = 1) : d116066 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d116066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28585 q ha hb
    | true =>
      simp only [d13051, d116066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28580 q ha hb
  have h11 (q : Pattern) (ha : d115396 q = 1) (hb : d115574 q = 1) : d116067 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d116067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115396, d116067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13092 q = 1) (hb : d115574 q = 1) : d116072 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d116072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28586 q ha hb
    | true =>
      simp only [d13092, d116072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13093 q = 1) (hb : d115574 q = 1) : d116073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d116073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13093, d116073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115397 q = 1) (hb : d115574 q = 1) : d116074 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d116074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115397, d116074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115398 q = 1) (hb : d115574 q = 1) : d116075 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d116075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115398, d116075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115399 q = 1) (hb : d115574 q = 1) : d116076 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d116076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115399, d116076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115400 q = 1) (hb : d115574 q = 1) : d116077 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d116077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d116077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28588 (p : Pattern) (ha : d13098 p = 1) (hb : d115574 p = 1) : d116078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d115574 q = 1) : d116013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28574 q ha hb
    | true =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d115574 q = 1) : d116014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d115574 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d115574 q = 1) : d116015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12975 q = 1) (hb : d115574 q = 1) : d116016 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12975, d116016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12975, d116016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13001 q = 1) (hb : d115574 q = 1) : d116037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13001, d116037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13001, d116037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13098 q = 1) (hb : d115574 q = 1) : d116078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13098, d116078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13098, d116078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28589 (p : Pattern) (ha : d13104 p = 1) (hb : d115574 p = 1) : d116083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d115574 q = 1) : d116013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28574 q ha hb
    | true =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d115574 q = 1) : d116014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d115574 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d12974 q = 1) (hb : d115574 q = 1) : d116015 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12974, d116015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13009 q = 1) (hb : d115574 q = 1) : d116043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13009, d116043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13009, d116043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13010 q = 1) (hb : d115574 q = 1) : d116044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13010, d116044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13010, d116044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13104 q = 1) (hb : d115574 q = 1) : d116083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13104, d116083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13104, d116083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28590 (p : Pattern) (ha : d13109 p = 1) (hb : d115574 p = 1) : d116087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13037 q = 1) (hb : d115574 q = 1) : d116052 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13037, d116052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28584 q ha hb
    | true =>
      simp only [d13037, d116052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13038 q = 1) (hb : d115574 q = 1) : d116053 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13038, d116053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13038, d116053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13041 q = 1) (hb : d115574 q = 1) : d116056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d116056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28579 q ha hb
    | true =>
      simp only [d13041, d116056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13042 q = 1) (hb : d115574 q = 1) : d116057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d116057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d116057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13043 q = 1) (hb : d115574 q = 1) : d116058 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13043, d116058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13043, d116058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13044 q = 1) (hb : d115574 q = 1) : d116059 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13044, d116059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13044, d116059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13045 q = 1) (hb : d115574 q = 1) : d116060 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13045, d116060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13045, d116060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13109 q = 1) (hb : d115574 q = 1) : d116087 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13109, d116087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13109, d116087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28591 (p : Pattern) (ha : d13110 p = 1) (hb : d115574 p = 1) : d116088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13041 q = 1) (hb : d115574 q = 1) : d116056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13041, d116056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28579 q ha hb
    | true =>
      simp only [d13041, d116056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13042 q = 1) (hb : d115574 q = 1) : d116057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13042, d116057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13042, d116057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12973 q = 1) (hb : d115574 q = 1) : d12973 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13047 q = 1) (hb : d115574 q = 1) : d116062 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13047, d116062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13047, d116062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13048 q = 1) (hb : d115574 q = 1) : d116063 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13048, d116063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13048, d116063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13049 q = 1) (hb : d115574 q = 1) : d116064 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13049, d116064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13049, d116064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13110 q = 1) (hb : d115574 q = 1) : d116088 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13110, d116088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13110, d116088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28592 (p : Pattern) (ha : d13116 p = 1) (hb : d115574 p = 1) : d116091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12968 q = 1) (hb : d115574 q = 1) : d116013 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28574 q ha hb
    | true =>
      simp only [d12968, d116013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12969 q = 1) (hb : d115574 q = 1) : d116014 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12969, d116014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13088 q = 1) (hb : d115574 q = 1) : d116068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13088, d116068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13088, d116068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13089 q = 1) (hb : d115574 q = 1) : d116069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13089, d116069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13089, d116069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13090 q = 1) (hb : d115574 q = 1) : d116070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13090, d116070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13090, d116070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13116 q = 1) (hb : d115574 q = 1) : d116091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13116, d116091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13116, d116091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28593 (p : Pattern) (ha : d115405 p = 1) (hb : d115574 p = 1) : d116097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13004 q = 1) (hb : d115574 q = 1) : d13004 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13005 q = 1) (hb : d115574 q = 1) : d116039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13005, d116039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28582 q ha hb
    | true =>
      simp only [d13005, d116039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13006 q = 1) (hb : d115574 q = 1) : d116040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13006, d116040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13006, d116040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13007 q = 1) (hb : d115574 q = 1) : d116041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13007, d116041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13007, d116041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13008 q = 1) (hb : d115574 q = 1) : d116042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13008, d116042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13008, d116042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13014 q = 1) (hb : d115574 q = 1) : d13014 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13015 q = 1) (hb : d115574 q = 1) : d116046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13015, d116046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28583 q ha hb
    | true =>
      simp only [d13015, d116046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13016 q = 1) (hb : d115574 q = 1) : d116047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13016, d116047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13016, d116047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13017 q = 1) (hb : d115574 q = 1) : d116048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13017, d116048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13017, d116048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13051 q = 1) (hb : d115574 q = 1) : d116066 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13051, d116066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28585 q ha hb
    | true =>
      simp only [d13051, d116066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28580 q ha hb
  have h11 (q : Pattern) (ha : d115396 q = 1) (hb : d115574 q = 1) : d116067 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d116067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115396, d116067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13092 q = 1) (hb : d115574 q = 1) : d116072 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13092, d116072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28586 q ha hb
    | true =>
      simp only [d13092, d116072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13093 q = 1) (hb : d115574 q = 1) : d116073 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13093, d116073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13093, d116073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115397 q = 1) (hb : d115574 q = 1) : d116074 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d116074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115397, d116074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115398 q = 1) (hb : d115574 q = 1) : d116075 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d116075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115398, d116075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115399 q = 1) (hb : d115574 q = 1) : d116076 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d116076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115399, d116076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13099 q = 1) (hb : d115574 q = 1) : d13099 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13100 q = 1) (hb : d115574 q = 1) : d116079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13100, d116079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28588 q ha hb
    | true =>
      simp only [d13100, d116079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13101 q = 1) (hb : d115574 q = 1) : d116080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13101, d116080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13101, d116080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d13102 q = 1) (hb : d115574 q = 1) : d116081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13102, d116081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d13102, d116081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d13103 q = 1) (hb : d115574 q = 1) : d116082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13103, d116082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13103, d116082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13105 q = 1) (hb : d115574 q = 1) : d13105 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d13106 q = 1) (hb : d115574 q = 1) : d116084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13106, d116084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28589 q ha hb
    | true =>
      simp only [d13106, d116084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d13107 q = 1) (hb : d115574 q = 1) : d116085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13107, d116085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13107, d116085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d13108 q = 1) (hb : d115574 q = 1) : d116086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13108, d116086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13108, d116086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d13111 q = 1) (hb : d115574 q = 1) : d116089 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d116089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28590 q ha hb
    | true =>
      simp only [d13111, d116089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28591 q ha hb
  have h27 (q : Pattern) (ha : d115401 q = 1) (hb : d115574 q = 1) : d116090 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d116090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115401, d116090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d13117 q = 1) (hb : d115574 q = 1) : d116092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d116092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28592 q ha hb
    | true =>
      simp only [d13117, d116092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d13118 q = 1) (hb : d115574 q = 1) : d116093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d116093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d13118, d116093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115402 q = 1) (hb : d115574 q = 1) : d116094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d116094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115402, d116094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115403 q = 1) (hb : d115574 q = 1) : d116095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d116095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115403, d116095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115404 q = 1) (hb : d115574 q = 1) : d116096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d116096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115404, d116096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115405 q = 1) (hb : d115574 q = 1) : d116097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d116097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115405, d116097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro28594 (p : Pattern) (ha : d115412 p = 1) (hb : d115574 p = 1) : d116111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13111 q = 1) (hb : d115574 q = 1) : d116089 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13111, d116089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28590 q ha hb
    | true =>
      simp only [d13111, d116089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28591 q ha hb
  have h2 (q : Pattern) (ha : d115401 q = 1) (hb : d115574 q = 1) : d116090 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d116090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115401, d116090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13117 q = 1) (hb : d115574 q = 1) : d116092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13117, d116092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28592 q ha hb
    | true =>
      simp only [d13117, d116092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13118 q = 1) (hb : d115574 q = 1) : d116093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13118, d116093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13118, d116093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d115574 q = 1) : d116094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d116094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115402, d116094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d115574 q = 1) : d116109 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d116109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d116109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d115574 q = 1) : d116110 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d116110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d116110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d115574 q = 1) : d116111 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d116111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d116111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28595 (p : Pattern) (ha : d13179 p = 1) (hb : d115574 p = 1) : d116120 p = 1 := by
  have h0 (q : Pattern) (ha : d13159 q = 1) (hb : d94753 q = 1) : d13159 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13173 q = 1) (hb : d115574 q = 1) : d116117 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13173, d115574, d116117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13173, d115574, d116117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13176 q = 1) (hb : d94753 q = 1) : d13176 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6358 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13177 q = 1) (hb : d115574 q = 1) : d116118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d115574, d116118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13177, d115574, d116118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13178 q = 1) (hb : d115574 q = 1) : d116119 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13178, d116119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13178, d116119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13179 q = 1) (hb : d115574 q = 1) : d116120 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13179, d116120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13179, d116120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28596 (p : Pattern) (ha : d13183 p = 1) (hb : d115574 p = 1) : d116124 p = 1 := by
  have h0 (q : Pattern) (ha : d13176 q = 1) (hb : d94753 q = 1) : d13176 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13177 q = 1) (hb : d115574 q = 1) : d116118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d115574, d116118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13177, d115574, d116118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6359 q = 1) (hb : d115574 q = 1) : d6359 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13182 q = 1) (hb : d115574 q = 1) : d116123 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13182, d116123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13182, d116123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13183 q = 1) (hb : d115574 q = 1) : d116124 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13183, d116124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13183, d116124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28597 (p : Pattern) (ha : d13189 p = 1) (hb : d115574 p = 1) : d116130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13180 q = 1) (hb : d115574 q = 1) : d116121 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13180, d116121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28595 q ha hb
    | true =>
      simp only [d13180, d116121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13181 q = 1) (hb : d115574 q = 1) : d116122 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13181, d116122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13181, d116122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13184 q = 1) (hb : d115574 q = 1) : d116125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d116125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28596 q ha hb
    | true =>
      simp only [d13184, d116125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13185 q = 1) (hb : d115574 q = 1) : d116126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d116126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d116126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13186 q = 1) (hb : d115574 q = 1) : d116127 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13186, d116127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13186, d116127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13187 q = 1) (hb : d115574 q = 1) : d116128 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13187, d116128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13187, d116128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13188 q = 1) (hb : d115574 q = 1) : d116129 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13188, d116129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13188, d116129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13189 q = 1) (hb : d115574 q = 1) : d116130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13189, d116130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13189, d116130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28598 (p : Pattern) (ha : d13202 p = 1) (hb : d115574 p = 1) : d116134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13184 q = 1) (hb : d115574 q = 1) : d116125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13184, d116125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28596 q ha hb
    | true =>
      simp only [d13184, d116125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13185 q = 1) (hb : d115574 q = 1) : d116126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13185, d116126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13185, d116126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13198 q = 1) (hb : d115574 q = 1) : d13198 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13199 q = 1) (hb : d115574 q = 1) : d116131 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13199, d116131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13199, d116131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13200 q = 1) (hb : d115574 q = 1) : d116132 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13200, d116132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13200, d116132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13201 q = 1) (hb : d115574 q = 1) : d116133 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13201, d116133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13201, d116133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13202 q = 1) (hb : d115574 q = 1) : d116134 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13202, d116134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13202, d116134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28599 (p : Pattern) (ha : d13243 p = 1) (hb : d115574 p = 1) : d116138 p = 1 := by
  have h0 (q : Pattern) (ha : d13176 q = 1) (hb : d94753 q = 1) : d13176 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6358 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13177 q = 1) (hb : d115574 q = 1) : d116118 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13177, d115574, d116118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13177, d115574, d116118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13194 q = 1) (hb : d115574 q = 1) : d13194 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13242 q = 1) (hb : d115574 q = 1) : d116137 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13242, d116137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13242, d116137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13243 q = 1) (hb : d115574 q = 1) : d116138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13243, d116138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13243, d116138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28600 (p : Pattern) (ha : d13249 p = 1) (hb : d115574 p = 1) : d116144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d115574 q = 1) : d116139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d116139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28599 q ha hb
    | true =>
      simp only [d13244, d116139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d115574 q = 1) : d116140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d116140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d116140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13246 q = 1) (hb : d115574 q = 1) : d116141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13246, d116141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13246, d116141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13247 q = 1) (hb : d115574 q = 1) : d116142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13247, d116142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13247, d116142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13248 q = 1) (hb : d115574 q = 1) : d116143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13248, d116143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13248, d116143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13249 q = 1) (hb : d115574 q = 1) : d116144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13249, d116144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13249, d116144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28601 (p : Pattern) (ha : d115422 p = 1) (hb : d115574 p = 1) : d116150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13203 q = 1) (hb : d115574 q = 1) : d116135 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13203, d116135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28597 q ha hb
    | true =>
      simp only [d13203, d116135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28598 q ha hb
  have h2 (q : Pattern) (ha : d115418 q = 1) (hb : d115574 q = 1) : d116136 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d116136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115418, d116136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13250 q = 1) (hb : d115574 q = 1) : d116145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13250, d116145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28600 q ha hb
    | true =>
      simp only [d13250, d116145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13251 q = 1) (hb : d115574 q = 1) : d116146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13251, d116146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13251, d116146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d115574 q = 1) : d116147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d116147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115419, d116147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d115574 q = 1) : d116148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d116148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d116148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d115574 q = 1) : d116149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d116149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d116149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d115574 q = 1) : d116150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d116150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d116150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28602 (p : Pattern) (ha : d115428 p = 1) (hb : d115574 p = 1) : d116156 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12988 q = 1) (hb : d115574 q = 1) : d116025 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12988, d116025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12988, d116025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28576 q ha hb
  have h2 (q : Pattern) (ha : d12989 q = 1) (hb : d115574 q = 1) : d116026 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12989, d116026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12989, d116026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12998 q = 1) (hb : d115574 q = 1) : d116034 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d116034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28576 q ha hb
    | true =>
      simp only [d12998, d116034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28578 q ha hb
  have h4 (q : Pattern) (ha : d12999 q = 1) (hb : d115574 q = 1) : d116035 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d116035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12999, d116035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13000 q = 1) (hb : d115574 q = 1) : d116036 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13000, d116036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13000, d116036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115406 q = 1) (hb : d115574 q = 1) : d116098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d116098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28587 q ha hb
    | true =>
      simp only [d115406, d116098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28593 q ha hb
  have h7 (q : Pattern) (ha : d13140 q = 1) (hb : d115574 q = 1) : d13140 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13141 q = 1) (hb : d115574 q = 1) : d116105 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13141, d116105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28581 q ha hb
    | true =>
      simp only [d13141, d116105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115407 q = 1) (hb : d115574 q = 1) : d116106 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d116106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115407, d116106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115408 q = 1) (hb : d115574 q = 1) : d116107 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d116107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115408, d116107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115409 q = 1) (hb : d115574 q = 1) : d116108 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d116108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115409, d116108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115413 q = 1) (hb : d115574 q = 1) : d116112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d116112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115413, d116112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28594 q ha hb
  have h13 (q : Pattern) (ha : d13150 q = 1) (hb : d115574 q = 1) : d13150 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115414 q = 1) (hb : d115574 q = 1) : d116113 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d116113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115414, d116113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115415 q = 1) (hb : d115574 q = 1) : d116114 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d116114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115415, d116114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115416 q = 1) (hb : d115574 q = 1) : d116115 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d116115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115416, d116115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115417 q = 1) (hb : d115574 q = 1) : d116116 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d116116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115417, d116116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115423 q = 1) (hb : d115574 q = 1) : d116151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d116151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115423, d116151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28601 q ha hb
  have h19 (q : Pattern) (ha : d13267 q = 1) (hb : d115574 q = 1) : d13267 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115424 q = 1) (hb : d115574 q = 1) : d116152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d116152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115424, d116152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115425 q = 1) (hb : d115574 q = 1) : d116153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d116153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115425, d116153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115426 q = 1) (hb : d115574 q = 1) : d116154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d116154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115426, d116154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115427 q = 1) (hb : d115574 q = 1) : d116155 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d116155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115427, d116155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115428 q = 1) (hb : d115574 q = 1) : d116156 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d116156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115428, d116156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro28603 (p : Pattern) (ha : d115434 p = 1) (hb : d115574 p = 1) : d116162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d115574 q = 1) : d116157 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d116157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d116157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28602 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d115574 q = 1) : d116158 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d116158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d116158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d115574 q = 1) : d116159 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d116159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d116159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d115574 q = 1) : d116160 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d116160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d116160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d115574 q = 1) : d116161 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d116161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d116161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d115574 q = 1) : d116162 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d116162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d116162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28604 (p : Pattern) (ha : d13293 p = 1) (hb : d115574 p = 1) : d116168 p = 1 := by
  have h0 (q : Pattern) (ha : d13285 q = 1) (hb : d94753 q = 1) : d13285 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13286 q = 1) (hb : d115574 q = 1) : d116166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d115574, d116166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13286, d115574, d116166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13291 q = 1) (hb : d115574 q = 1) : d13291 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13292 q = 1) (hb : d115574 q = 1) : d116167 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13292, d116167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13292, d116167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13293 q = 1) (hb : d115574 q = 1) : d116168 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13293, d116168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13293, d116168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28605 (p : Pattern) (ha : d13303 p = 1) (hb : d115574 p = 1) : d116174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d115574 q = 1) : d116169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28604 q ha hb
    | true =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d115574 q = 1) : d116170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d115574 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d115574 q = 1) : d116171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13301 q = 1) (hb : d115574 q = 1) : d116172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d116172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13301, d116172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13302 q = 1) (hb : d115574 q = 1) : d116173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d116173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13302, d116173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13303 q = 1) (hb : d115574 q = 1) : d116174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13303, d116174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13303, d116174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28606 (p : Pattern) (ha : d13313 p = 1) (hb : d115574 p = 1) : d116180 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13307 q = 1) (hb : d115574 q = 1) : d13307 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13308 q = 1) (hb : d115574 q = 1) : d116175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d116175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28605 q ha hb
    | true =>
      simp only [d13308, d116175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13309 q = 1) (hb : d115574 q = 1) : d116176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d116176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d116176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13310 q = 1) (hb : d115574 q = 1) : d116177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d116177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13310, d116177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13311 q = 1) (hb : d115574 q = 1) : d116178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d116178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d116178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13312 q = 1) (hb : d115574 q = 1) : d116179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d116179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d116179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13313 q = 1) (hb : d115574 q = 1) : d116180 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13313, d116180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13313, d116180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28607 (p : Pattern) (ha : d13316 p = 1) (hb : d115574 p = 1) : d116183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d115574 q = 1) : d116169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28604 q ha hb
    | true =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d115574 q = 1) : d116170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d115574 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d115574 q = 1) : d116171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13301 q = 1) (hb : d115574 q = 1) : d116172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d116172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13301, d116172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13302 q = 1) (hb : d115574 q = 1) : d116173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13302, d116173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13302, d116173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13316 q = 1) (hb : d115574 q = 1) : d116183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13316, d116183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13316, d116183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28608 (p : Pattern) (ha : d13323 p = 1) (hb : d115574 p = 1) : d116189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13307 q = 1) (hb : d115574 q = 1) : d13307 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13308 q = 1) (hb : d115574 q = 1) : d116175 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13308, d116175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28605 q ha hb
    | true =>
      simp only [d13308, d116175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13309 q = 1) (hb : d115574 q = 1) : d116176 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13309, d116176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13309, d116176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13310 q = 1) (hb : d115574 q = 1) : d116177 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13310, d116177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13310, d116177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13311 q = 1) (hb : d115574 q = 1) : d116178 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13311, d116178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13311, d116178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13312 q = 1) (hb : d115574 q = 1) : d116179 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13312, d116179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13312, d116179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13317 q = 1) (hb : d115574 q = 1) : d13317 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13318 q = 1) (hb : d115574 q = 1) : d116184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d116184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28607 q ha hb
    | true =>
      simp only [d13318, d116184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13319 q = 1) (hb : d115574 q = 1) : d116185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d116185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d116185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13320 q = 1) (hb : d115574 q = 1) : d116186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d116186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13320, d116186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13321 q = 1) (hb : d115574 q = 1) : d116187 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d116187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d116187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13322 q = 1) (hb : d115574 q = 1) : d116188 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d116188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d116188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13323 q = 1) (hb : d115574 q = 1) : d116189 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13323, d116189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13323, d116189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro28609 (p : Pattern) (ha : d13366 p = 1) (hb : d115574 p = 1) : d116211 p = 1 := by
  have h0 (q : Pattern) (ha : d13285 q = 1) (hb : d94753 q = 1) : d13285 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5142 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13286 q = 1) (hb : d115574 q = 1) : d116166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d115574, d116166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13286, d115574, d116166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5143 q = 1) (hb : d115574 q = 1) : d5143 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13365 q = 1) (hb : d115574 q = 1) : d116210 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13365, d116210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13365, d116210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13366 q = 1) (hb : d115574 q = 1) : d116211 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13366, d116211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13366, d116211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28610 (p : Pattern) (ha : d13376 p = 1) (hb : d115574 p = 1) : d116221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d115574 q = 1) : d116212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d116212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28609 q ha hb
    | true =>
      simp only [d13367, d116212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d115574 q = 1) : d116213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d116213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d116213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d115574 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13373 q = 1) (hb : d115574 q = 1) : d116218 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d116218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d116218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13374 q = 1) (hb : d115574 q = 1) : d116219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d116219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13374, d116219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13375 q = 1) (hb : d115574 q = 1) : d116220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d116220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13375, d116220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13376 q = 1) (hb : d115574 q = 1) : d116221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13376, d116221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13376, d116221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28611 (p : Pattern) (ha : d13460 p = 1) (hb : d115574 p = 1) : d116260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13307 q = 1) (hb : d115574 q = 1) : d13307 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13450 q = 1) (hb : d115574 q = 1) : d116255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13450, d116255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28610 q ha hb
    | true =>
      simp only [d13450, d116255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13451 q = 1) (hb : d115574 q = 1) : d116256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13451, d116256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13451, d116256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13452 q = 1) (hb : d115574 q = 1) : d116257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13452, d116257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13452, d116257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13453 q = 1) (hb : d115574 q = 1) : d116258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13453, d116258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13453, d116258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13454 q = 1) (hb : d115574 q = 1) : d116259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13454, d116259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13454, d116259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13459 q = 1) (hb : d115574 q = 1) : d13459 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13460 q = 1) (hb : d115574 q = 1) : d116260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13460, d116260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13460, d116260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28612 (p : Pattern) (ha : d13328 p = 1) (hb : d115574 p = 1) : d116194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d115574 q = 1) : d116169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28604 q ha hb
    | true =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d115574 q = 1) : d116170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d115574 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d115574 q = 1) : d116171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13301 q = 1) (hb : d115574 q = 1) : d116172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d116172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13301, d116172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13327 q = 1) (hb : d115574 q = 1) : d116193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d116193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d116193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13328 q = 1) (hb : d115574 q = 1) : d116194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13328, d116194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13328, d116194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28613 (p : Pattern) (ha : d13337 p = 1) (hb : d115574 p = 1) : d116201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d115574 q = 1) : d116169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28604 q ha hb
    | true =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d115574 q = 1) : d116170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d115574 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d115574 q = 1) : d116171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13335 q = 1) (hb : d115574 q = 1) : d116199 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d116199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d116199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13336 q = 1) (hb : d115574 q = 1) : d116200 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d116200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13336, d116200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13337 q = 1) (hb : d115574 q = 1) : d116201 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13337, d116201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13337, d116201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28614 (p : Pattern) (ha : d13362 p = 1) (hb : d115574 p = 1) : d116207 p = 1 := by
  have h0 (q : Pattern) (ha : d13347 q = 1) (hb : d94753 q = 1) : d13347 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13359 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13360 q = 1) (hb : d115574 q = 1) : d116205 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13360, d115574, d116205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13360, d115574, d116205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13285 q = 1) (hb : d94753 q = 1) : d13285 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5142 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13286 q = 1) (hb : d115574 q = 1) : d116166 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13286, d115574, d116166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13286, d115574, d116166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13361 q = 1) (hb : d115574 q = 1) : d116206 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13361, d116206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13361, d116206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13362 q = 1) (hb : d115574 q = 1) : d116207 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13362, d116207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13362, d116207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28615 (p : Pattern) (ha : d13372 p = 1) (hb : d115574 p = 1) : d116217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d115574 q = 1) : d116208 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d116208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28614 q ha hb
    | true =>
      simp only [d13363, d116208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d115574 q = 1) : d116209 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d116209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d116209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d115574 q = 1) : d116212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d116212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28609 q ha hb
    | true =>
      simp only [d13367, d116212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d115574 q = 1) : d116213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d116213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d116213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d115574 q = 1) : d116214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d116214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d116214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d115574 q = 1) : d116215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d116215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d116215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d115574 q = 1) : d116216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d116216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d116216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13372 q = 1) (hb : d115574 q = 1) : d116217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13372, d116217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13372, d116217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28616 (p : Pattern) (ha : d13417 p = 1) (hb : d115574 p = 1) : d116227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d115574 q = 1) : d116169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28604 q ha hb
    | true =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d115574 q = 1) : d116170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d115574 q = 1) : d116224 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d116224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d116224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d115574 q = 1) : d116225 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d116225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d116225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d115574 q = 1) : d116226 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d116226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d116226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13417 q = 1) (hb : d115574 q = 1) : d116227 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13417, d116227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13417, d116227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28617 (p : Pattern) (ha : d115442 p = 1) (hb : d115574 p = 1) : d116233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13330 q = 1) (hb : d115574 q = 1) : d13330 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13331 q = 1) (hb : d115574 q = 1) : d116195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d116195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28612 q ha hb
    | true =>
      simp only [d13331, d116195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13332 q = 1) (hb : d115574 q = 1) : d116196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d116196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d116196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13333 q = 1) (hb : d115574 q = 1) : d116197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d116197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13333, d116197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13334 q = 1) (hb : d115574 q = 1) : d116198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d116198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d116198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d115574 q = 1) : d13340 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13341 q = 1) (hb : d115574 q = 1) : d116202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d116202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28613 q ha hb
    | true =>
      simp only [d13341, d116202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13342 q = 1) (hb : d115574 q = 1) : d116203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d116203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d116203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13343 q = 1) (hb : d115574 q = 1) : d116204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d116204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13343, d116204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13377 q = 1) (hb : d115574 q = 1) : d116222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d116222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28615 q ha hb
    | true =>
      simp only [d13377, d116222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28610 q ha hb
  have h11 (q : Pattern) (ha : d115438 q = 1) (hb : d115574 q = 1) : d116223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d116223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115438, d116223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13418 q = 1) (hb : d115574 q = 1) : d116228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d116228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28616 q ha hb
    | true =>
      simp only [d13418, d116228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13419 q = 1) (hb : d115574 q = 1) : d116229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d116229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13419, d116229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115439 q = 1) (hb : d115574 q = 1) : d116230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d116230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115439, d116230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115440 q = 1) (hb : d115574 q = 1) : d116231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d116231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115440, d116231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115441 q = 1) (hb : d115574 q = 1) : d116232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d116232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115441, d116232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115442 q = 1) (hb : d115574 q = 1) : d116233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d116233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d116233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28618 (p : Pattern) (ha : d13424 p = 1) (hb : d115574 p = 1) : d116234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d115574 q = 1) : d116169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28604 q ha hb
    | true =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d115574 q = 1) : d116170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d115574 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d115574 q = 1) : d116171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13301 q = 1) (hb : d115574 q = 1) : d116172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13301, d116172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13301, d116172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13327 q = 1) (hb : d115574 q = 1) : d116193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13327, d116193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13327, d116193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13424 q = 1) (hb : d115574 q = 1) : d116234 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13424, d116234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13424, d116234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28619 (p : Pattern) (ha : d13430 p = 1) (hb : d115574 p = 1) : d116239 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d115574 q = 1) : d116169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28604 q ha hb
    | true =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d115574 q = 1) : d116170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d115574 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13300 q = 1) (hb : d115574 q = 1) : d116171 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13300, d116171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13335 q = 1) (hb : d115574 q = 1) : d116199 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13335, d116199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13335, d116199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13336 q = 1) (hb : d115574 q = 1) : d116200 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13336, d116200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13336, d116200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13430 q = 1) (hb : d115574 q = 1) : d116239 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13430, d116239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13430, d116239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28620 (p : Pattern) (ha : d13435 p = 1) (hb : d115574 p = 1) : d116243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13363 q = 1) (hb : d115574 q = 1) : d116208 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13363, d116208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28614 q ha hb
    | true =>
      simp only [d13363, d116208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13364 q = 1) (hb : d115574 q = 1) : d116209 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13364, d116209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13364, d116209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13367 q = 1) (hb : d115574 q = 1) : d116212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d116212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28609 q ha hb
    | true =>
      simp only [d13367, d116212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13368 q = 1) (hb : d115574 q = 1) : d116213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d116213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d116213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13369 q = 1) (hb : d115574 q = 1) : d116214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13369, d116214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13369, d116214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13370 q = 1) (hb : d115574 q = 1) : d116215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13370, d116215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13370, d116215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13371 q = 1) (hb : d115574 q = 1) : d116216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13371, d116216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13371, d116216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13435 q = 1) (hb : d115574 q = 1) : d116243 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13435, d116243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13435, d116243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28621 (p : Pattern) (ha : d13436 p = 1) (hb : d115574 p = 1) : d116244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13367 q = 1) (hb : d115574 q = 1) : d116212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13367, d116212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28609 q ha hb
    | true =>
      simp only [d13367, d116212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13368 q = 1) (hb : d115574 q = 1) : d116213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13368, d116213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13368, d116213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13299 q = 1) (hb : d115574 q = 1) : d13299 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13373 q = 1) (hb : d115574 q = 1) : d116218 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13373, d116218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13373, d116218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13374 q = 1) (hb : d115574 q = 1) : d116219 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13374, d116219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13374, d116219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13375 q = 1) (hb : d115574 q = 1) : d116220 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13375, d116220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13375, d116220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13436 q = 1) (hb : d115574 q = 1) : d116244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13436, d116244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13436, d116244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28622 (p : Pattern) (ha : d13442 p = 1) (hb : d115574 p = 1) : d116247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13294 q = 1) (hb : d115574 q = 1) : d116169 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28604 q ha hb
    | true =>
      simp only [d13294, d116169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13295 q = 1) (hb : d115574 q = 1) : d116170 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13295, d116170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13414 q = 1) (hb : d115574 q = 1) : d116224 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13414, d116224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13414, d116224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13415 q = 1) (hb : d115574 q = 1) : d116225 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13415, d116225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13415, d116225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13416 q = 1) (hb : d115574 q = 1) : d116226 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13416, d116226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13416, d116226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13442 q = 1) (hb : d115574 q = 1) : d116247 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13442, d116247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13442, d116247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28623 (p : Pattern) (ha : d115447 p = 1) (hb : d115574 p = 1) : d116253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13330 q = 1) (hb : d115574 q = 1) : d13330 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13331 q = 1) (hb : d115574 q = 1) : d116195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13331, d116195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28612 q ha hb
    | true =>
      simp only [d13331, d116195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13332 q = 1) (hb : d115574 q = 1) : d116196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13332, d116196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13332, d116196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13333 q = 1) (hb : d115574 q = 1) : d116197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13333, d116197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13333, d116197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13334 q = 1) (hb : d115574 q = 1) : d116198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13334, d116198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13334, d116198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13340 q = 1) (hb : d115574 q = 1) : d13340 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13341 q = 1) (hb : d115574 q = 1) : d116202 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13341, d116202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28613 q ha hb
    | true =>
      simp only [d13341, d116202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13342 q = 1) (hb : d115574 q = 1) : d116203 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13342, d116203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13342, d116203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13343 q = 1) (hb : d115574 q = 1) : d116204 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13343, d116204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13343, d116204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13377 q = 1) (hb : d115574 q = 1) : d116222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13377, d116222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28615 q ha hb
    | true =>
      simp only [d13377, d116222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28610 q ha hb
  have h11 (q : Pattern) (ha : d115438 q = 1) (hb : d115574 q = 1) : d116223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d116223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115438, d116223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13418 q = 1) (hb : d115574 q = 1) : d116228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13418, d116228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28616 q ha hb
    | true =>
      simp only [d13418, d116228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13419 q = 1) (hb : d115574 q = 1) : d116229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13419, d116229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13419, d116229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115439 q = 1) (hb : d115574 q = 1) : d116230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d116230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115439, d116230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115440 q = 1) (hb : d115574 q = 1) : d116231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d116231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115440, d116231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115441 q = 1) (hb : d115574 q = 1) : d116232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d116232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115441, d116232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13425 q = 1) (hb : d115574 q = 1) : d13425 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13426 q = 1) (hb : d115574 q = 1) : d116235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13426, d116235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28618 q ha hb
    | true =>
      simp only [d13426, d116235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13427 q = 1) (hb : d115574 q = 1) : d116236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13427, d116236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13427, d116236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d13428 q = 1) (hb : d115574 q = 1) : d116237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13428, d116237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d13428, d116237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d13429 q = 1) (hb : d115574 q = 1) : d116238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13429, d116238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13429, d116238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13431 q = 1) (hb : d115574 q = 1) : d13431 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d13432 q = 1) (hb : d115574 q = 1) : d116240 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13432, d116240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28619 q ha hb
    | true =>
      simp only [d13432, d116240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d13433 q = 1) (hb : d115574 q = 1) : d116241 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13433, d116241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13433, d116241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d13434 q = 1) (hb : d115574 q = 1) : d116242 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13434, d116242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13434, d116242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d13437 q = 1) (hb : d115574 q = 1) : d116245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d116245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28620 q ha hb
    | true =>
      simp only [d13437, d116245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28621 q ha hb
  have h27 (q : Pattern) (ha : d115443 q = 1) (hb : d115574 q = 1) : d116246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d116246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115443, d116246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d13443 q = 1) (hb : d115574 q = 1) : d116248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d116248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28622 q ha hb
    | true =>
      simp only [d13443, d116248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d13444 q = 1) (hb : d115574 q = 1) : d116249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d116249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d13444, d116249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115444 q = 1) (hb : d115574 q = 1) : d116250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d116250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115444, d116250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115445 q = 1) (hb : d115574 q = 1) : d116251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d116251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115445, d116251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115446 q = 1) (hb : d115574 q = 1) : d116252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d116252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115446, d116252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115447 q = 1) (hb : d115574 q = 1) : d116253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d116253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115447, d116253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro28624 (p : Pattern) (ha : d115454 p = 1) (hb : d115574 p = 1) : d116267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13437 q = 1) (hb : d115574 q = 1) : d116245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13437, d116245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28620 q ha hb
    | true =>
      simp only [d13437, d116245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28621 q ha hb
  have h2 (q : Pattern) (ha : d115443 q = 1) (hb : d115574 q = 1) : d116246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d116246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115443, d116246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13443 q = 1) (hb : d115574 q = 1) : d116248 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13443, d116248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28622 q ha hb
    | true =>
      simp only [d13443, d116248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13444 q = 1) (hb : d115574 q = 1) : d116249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13444, d116249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13444, d116249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115444 q = 1) (hb : d115574 q = 1) : d116250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d116250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115444, d116250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115452 q = 1) (hb : d115574 q = 1) : d116265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d116265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115452, d116265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115453 q = 1) (hb : d115574 q = 1) : d116266 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d116266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115453, d116266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115454 q = 1) (hb : d115574 q = 1) : d116267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d116267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115454, d116267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28625 (p : Pattern) (ha : d13505 p = 1) (hb : d115574 p = 1) : d116276 p = 1 := by
  have h0 (q : Pattern) (ha : d13485 q = 1) (hb : d94753 q = 1) : d13485 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13498 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13499 q = 1) (hb : d115574 q = 1) : d116273 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13499, d115574, d116273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13499, d115574, d116273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13502 q = 1) (hb : d94753 q = 1) : d13502 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6504 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13503 q = 1) (hb : d115574 q = 1) : d116274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d115574, d116274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13503, d115574, d116274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13504 q = 1) (hb : d115574 q = 1) : d116275 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13504, d116275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13504, d116275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13505 q = 1) (hb : d115574 q = 1) : d116276 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13505, d116276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13505, d116276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28626 (p : Pattern) (ha : d13509 p = 1) (hb : d115574 p = 1) : d116280 p = 1 := by
  have h0 (q : Pattern) (ha : d13502 q = 1) (hb : d94753 q = 1) : d13502 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13503 q = 1) (hb : d115574 q = 1) : d116274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d115574, d116274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13503, d115574, d116274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6505 q = 1) (hb : d115574 q = 1) : d6505 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13508 q = 1) (hb : d115574 q = 1) : d116279 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13508, d116279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13508, d116279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13509 q = 1) (hb : d115574 q = 1) : d116280 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13509, d116280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13509, d116280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28627 (p : Pattern) (ha : d13515 p = 1) (hb : d115574 p = 1) : d116286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13506 q = 1) (hb : d115574 q = 1) : d116277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13506, d116277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28625 q ha hb
    | true =>
      simp only [d13506, d116277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13507 q = 1) (hb : d115574 q = 1) : d116278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13507, d116278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13507, d116278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13510 q = 1) (hb : d115574 q = 1) : d116281 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d116281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28626 q ha hb
    | true =>
      simp only [d13510, d116281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13511 q = 1) (hb : d115574 q = 1) : d116282 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d116282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d116282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13512 q = 1) (hb : d115574 q = 1) : d116283 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13512, d116283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13512, d116283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13513 q = 1) (hb : d115574 q = 1) : d116284 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13513, d116284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13513, d116284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13514 q = 1) (hb : d115574 q = 1) : d116285 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13514, d116285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13514, d116285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13515 q = 1) (hb : d115574 q = 1) : d116286 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13515, d116286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13515, d116286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28628 (p : Pattern) (ha : d13528 p = 1) (hb : d115574 p = 1) : d116290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13510 q = 1) (hb : d115574 q = 1) : d116281 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13510, d116281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28626 q ha hb
    | true =>
      simp only [d13510, d116281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13511 q = 1) (hb : d115574 q = 1) : d116282 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13511, d116282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13511, d116282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13524 q = 1) (hb : d115574 q = 1) : d13524 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13525 q = 1) (hb : d115574 q = 1) : d116287 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13525, d116287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13525, d116287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13526 q = 1) (hb : d115574 q = 1) : d116288 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13526, d116288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13526, d116288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13527 q = 1) (hb : d115574 q = 1) : d116289 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13527, d116289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13527, d116289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13528 q = 1) (hb : d115574 q = 1) : d116290 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13528, d116290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13528, d116290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28629 (p : Pattern) (ha : d13569 p = 1) (hb : d115574 p = 1) : d116294 p = 1 := by
  have h0 (q : Pattern) (ha : d13502 q = 1) (hb : d94753 q = 1) : d13502 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6504 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13503 q = 1) (hb : d115574 q = 1) : d116274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13503, d115574, d116274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13503, d115574, d116274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13520 q = 1) (hb : d115574 q = 1) : d13520 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13568 q = 1) (hb : d115574 q = 1) : d116293 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13568, d116293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13568, d116293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13569 q = 1) (hb : d115574 q = 1) : d116294 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13569, d116294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13569, d116294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28630 (p : Pattern) (ha : d13575 p = 1) (hb : d115574 p = 1) : d116300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d115574 q = 1) : d116295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d116295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28629 q ha hb
    | true =>
      simp only [d13570, d116295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d115574 q = 1) : d116296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d116296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d116296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13572 q = 1) (hb : d115574 q = 1) : d116297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13572, d116297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13572, d116297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13573 q = 1) (hb : d115574 q = 1) : d116298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13573, d116298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13573, d116298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13574 q = 1) (hb : d115574 q = 1) : d116299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13574, d116299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13574, d116299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13575 q = 1) (hb : d115574 q = 1) : d116300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13575, d116300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13575, d116300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28631 (p : Pattern) (ha : d115464 p = 1) (hb : d115574 p = 1) : d116306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13529 q = 1) (hb : d115574 q = 1) : d116291 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13529, d116291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28627 q ha hb
    | true =>
      simp only [d13529, d116291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28628 q ha hb
  have h2 (q : Pattern) (ha : d115460 q = 1) (hb : d115574 q = 1) : d116292 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d116292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115460, d116292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13576 q = 1) (hb : d115574 q = 1) : d116301 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13576, d116301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28630 q ha hb
    | true =>
      simp only [d13576, d116301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13577 q = 1) (hb : d115574 q = 1) : d116302 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13577, d116302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13577, d116302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115461 q = 1) (hb : d115574 q = 1) : d116303 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d116303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115461, d116303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115462 q = 1) (hb : d115574 q = 1) : d116304 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d116304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115462, d116304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115463 q = 1) (hb : d115574 q = 1) : d116305 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d116305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115463, d116305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115464 q = 1) (hb : d115574 q = 1) : d116306 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d116306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115464, d116306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28632 (p : Pattern) (ha : d115470 p = 1) (hb : d115574 p = 1) : d116312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13314 q = 1) (hb : d115574 q = 1) : d116181 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13314, d116181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13314, d116181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28606 q ha hb
  have h2 (q : Pattern) (ha : d13315 q = 1) (hb : d115574 q = 1) : d116182 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13315, d116182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13315, d116182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13324 q = 1) (hb : d115574 q = 1) : d116190 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d116190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28606 q ha hb
    | true =>
      simp only [d13324, d116190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28608 q ha hb
  have h4 (q : Pattern) (ha : d13325 q = 1) (hb : d115574 q = 1) : d116191 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d116191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13325, d116191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13326 q = 1) (hb : d115574 q = 1) : d116192 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13326, d116192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13326, d116192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115448 q = 1) (hb : d115574 q = 1) : d116254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d116254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28617 q ha hb
    | true =>
      simp only [d115448, d116254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28623 q ha hb
  have h7 (q : Pattern) (ha : d13466 q = 1) (hb : d115574 q = 1) : d13466 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13467 q = 1) (hb : d115574 q = 1) : d116261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13467, d116261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28611 q ha hb
    | true =>
      simp only [d13467, d116261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115449 q = 1) (hb : d115574 q = 1) : d116262 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d116262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115449, d116262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115450 q = 1) (hb : d115574 q = 1) : d116263 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d116263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115450, d116263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115451 q = 1) (hb : d115574 q = 1) : d116264 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d116264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115451, d116264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115455 q = 1) (hb : d115574 q = 1) : d116268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d116268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115455, d116268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28624 q ha hb
  have h13 (q : Pattern) (ha : d13476 q = 1) (hb : d115574 q = 1) : d13476 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115456 q = 1) (hb : d115574 q = 1) : d116269 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d116269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115456, d116269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115457 q = 1) (hb : d115574 q = 1) : d116270 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d116270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115457, d116270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115458 q = 1) (hb : d115574 q = 1) : d116271 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d116271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115458, d116271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115459 q = 1) (hb : d115574 q = 1) : d116272 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d116272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115459, d116272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115465 q = 1) (hb : d115574 q = 1) : d116307 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d116307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115465, d116307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28631 q ha hb
  have h19 (q : Pattern) (ha : d13593 q = 1) (hb : d115574 q = 1) : d13593 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115466 q = 1) (hb : d115574 q = 1) : d116308 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d116308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115466, d116308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115467 q = 1) (hb : d115574 q = 1) : d116309 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d116309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115467, d116309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115468 q = 1) (hb : d115574 q = 1) : d116310 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d116310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115468, d116310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115469 q = 1) (hb : d115574 q = 1) : d116311 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d116311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115469, d116311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115470 q = 1) (hb : d115574 q = 1) : d116312 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d116312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115470, d116312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro28633 (p : Pattern) (ha : d115476 p = 1) (hb : d115574 p = 1) : d116318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115471 q = 1) (hb : d115574 q = 1) : d116313 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d116313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115471, d116313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28632 q ha hb
  have h2 (q : Pattern) (ha : d115472 q = 1) (hb : d115574 q = 1) : d116314 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d116314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115472, d116314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115473 q = 1) (hb : d115574 q = 1) : d116315 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d116315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115473, d116315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115474 q = 1) (hb : d115574 q = 1) : d116316 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d116316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115474, d116316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115475 q = 1) (hb : d115574 q = 1) : d116317 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d116317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115475, d116317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115476 q = 1) (hb : d115574 q = 1) : d116318 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d116318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115476, d116318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28634 (p : Pattern) (ha : d13620 p = 1) (hb : d115574 p = 1) : d116325 p = 1 := by
  have h0 (q : Pattern) (ha : d13612 q = 1) (hb : d94753 q = 1) : d13612 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13613 q = 1) (hb : d115574 q = 1) : d116323 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d115574, d116323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13613, d115574, d116323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13618 q = 1) (hb : d115574 q = 1) : d13618 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13619 q = 1) (hb : d115574 q = 1) : d116324 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13619, d116324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13619, d116324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13620 q = 1) (hb : d115574 q = 1) : d116325 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13620, d116325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13620, d116325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28635 (p : Pattern) (ha : d13630 p = 1) (hb : d115574 p = 1) : d116331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d115574 q = 1) : d116326 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28634 q ha hb
    | true =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d115574 q = 1) : d116327 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d115574 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d115574 q = 1) : d116328 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13628 q = 1) (hb : d115574 q = 1) : d116329 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d116329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13628, d116329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13629 q = 1) (hb : d115574 q = 1) : d116330 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d116330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13629, d116330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13630 q = 1) (hb : d115574 q = 1) : d116331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13630, d116331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13630, d116331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28636 (p : Pattern) (ha : d13640 p = 1) (hb : d115574 p = 1) : d116337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13634 q = 1) (hb : d115574 q = 1) : d13634 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13635 q = 1) (hb : d115574 q = 1) : d116332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d116332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28635 q ha hb
    | true =>
      simp only [d13635, d116332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13636 q = 1) (hb : d115574 q = 1) : d116333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13637 q = 1) (hb : d115574 q = 1) : d116334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13637, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13638 q = 1) (hb : d115574 q = 1) : d116335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13639 q = 1) (hb : d115574 q = 1) : d116336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13640 q = 1) (hb : d115574 q = 1) : d116337 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13640, d116337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13640, d116337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28637 (p : Pattern) (ha : d13643 p = 1) (hb : d115574 p = 1) : d116340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d115574 q = 1) : d116326 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28634 q ha hb
    | true =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d115574 q = 1) : d116327 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d115574 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d115574 q = 1) : d116328 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13628 q = 1) (hb : d115574 q = 1) : d116329 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d116329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13628, d116329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13629 q = 1) (hb : d115574 q = 1) : d116330 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13629, d116330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13629, d116330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13643 q = 1) (hb : d115574 q = 1) : d116340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13643, d116340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13643, d116340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28638 (p : Pattern) (ha : d13650 p = 1) (hb : d115574 p = 1) : d116346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13634 q = 1) (hb : d115574 q = 1) : d13634 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13635 q = 1) (hb : d115574 q = 1) : d116332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13635, d116332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28635 q ha hb
    | true =>
      simp only [d13635, d116332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13636 q = 1) (hb : d115574 q = 1) : d116333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13636, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13636, d116333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13637 q = 1) (hb : d115574 q = 1) : d116334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13637, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13637, d116334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13638 q = 1) (hb : d115574 q = 1) : d116335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13638, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13638, d116335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13639 q = 1) (hb : d115574 q = 1) : d116336 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13639, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13639, d116336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13644 q = 1) (hb : d115574 q = 1) : d13644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13645 q = 1) (hb : d115574 q = 1) : d116341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d116341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28637 q ha hb
    | true =>
      simp only [d13645, d116341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13646 q = 1) (hb : d115574 q = 1) : d116342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d116342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13647 q = 1) (hb : d115574 q = 1) : d116343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13647, d116343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13648 q = 1) (hb : d115574 q = 1) : d116344 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d116344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13649 q = 1) (hb : d115574 q = 1) : d116345 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d116345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d13650 q = 1) (hb : d115574 q = 1) : d116346 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13650, d116346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13650, d116346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro28639 (p : Pattern) (ha : d13693 p = 1) (hb : d115574 p = 1) : d116368 p = 1 := by
  have h0 (q : Pattern) (ha : d13612 q = 1) (hb : d94753 q = 1) : d13612 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5255 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13613 q = 1) (hb : d115574 q = 1) : d116323 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d115574, d116323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13613, d115574, d116323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5256 q = 1) (hb : d115574 q = 1) : d5256 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13692 q = 1) (hb : d115574 q = 1) : d116367 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13692, d116367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13692, d116367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13693 q = 1) (hb : d115574 q = 1) : d116368 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13693, d116368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13693, d116368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28640 (p : Pattern) (ha : d13703 p = 1) (hb : d115574 p = 1) : d116378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d115574 q = 1) : d116369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d116369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28639 q ha hb
    | true =>
      simp only [d13694, d116369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d115574 q = 1) : d116370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d116370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d116370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d115574 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13700 q = 1) (hb : d115574 q = 1) : d116375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d116375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d116375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13701 q = 1) (hb : d115574 q = 1) : d116376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d116376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13701, d116376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13702 q = 1) (hb : d115574 q = 1) : d116377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d116377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13702, d116377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13703 q = 1) (hb : d115574 q = 1) : d116378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13703, d116378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13703, d116378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28641 (p : Pattern) (ha : d13787 p = 1) (hb : d115574 p = 1) : d116417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13634 q = 1) (hb : d115574 q = 1) : d13634 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13777 q = 1) (hb : d115574 q = 1) : d116412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13777, d116412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28640 q ha hb
    | true =>
      simp only [d13777, d116412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13778 q = 1) (hb : d115574 q = 1) : d116413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13778, d116413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13778, d116413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13779 q = 1) (hb : d115574 q = 1) : d116414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13779, d116414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13779, d116414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13780 q = 1) (hb : d115574 q = 1) : d116415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13780, d116415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13780, d116415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13781 q = 1) (hb : d115574 q = 1) : d116416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13781, d116416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13781, d116416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13786 q = 1) (hb : d115574 q = 1) : d13786 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13787 q = 1) (hb : d115574 q = 1) : d116417 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d13787, d116417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13787, d116417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28642 (p : Pattern) (ha : d13655 p = 1) (hb : d115574 p = 1) : d116351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d115574 q = 1) : d116326 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28634 q ha hb
    | true =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d115574 q = 1) : d116327 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d115574 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d115574 q = 1) : d116328 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13628 q = 1) (hb : d115574 q = 1) : d116329 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d116329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13628, d116329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13654 q = 1) (hb : d115574 q = 1) : d116350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d116350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d116350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13655 q = 1) (hb : d115574 q = 1) : d116351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13655, d116351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13655, d116351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28643 (p : Pattern) (ha : d13664 p = 1) (hb : d115574 p = 1) : d116358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d115574 q = 1) : d116326 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28634 q ha hb
    | true =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d115574 q = 1) : d116327 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d115574 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d115574 q = 1) : d116328 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13662 q = 1) (hb : d115574 q = 1) : d116356 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d116356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d116356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13663 q = 1) (hb : d115574 q = 1) : d116357 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d116357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13663, d116357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13664 q = 1) (hb : d115574 q = 1) : d116358 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13664, d116358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13664, d116358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro28644 (p : Pattern) (ha : d13689 p = 1) (hb : d115574 p = 1) : d116364 p = 1 := by
  have h0 (q : Pattern) (ha : d13674 q = 1) (hb : d94753 q = 1) : d13674 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13687 q = 1) (hb : d115574 q = 1) : d116362 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13687, d115574, d116362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13687, d115574, d116362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13612 q = 1) (hb : d94753 q = 1) : d13612 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5255 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13613 q = 1) (hb : d115574 q = 1) : d116323 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13613, d115574, d116323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13613, d115574, d116323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13688 q = 1) (hb : d115574 q = 1) : d116363 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13688, d116363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13688, d116363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13689 q = 1) (hb : d115574 q = 1) : d116364 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13689, d116364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13689, d116364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28645 (p : Pattern) (ha : d13699 p = 1) (hb : d115574 p = 1) : d116374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d115574 q = 1) : d116365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d116365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28644 q ha hb
    | true =>
      simp only [d13690, d116365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d115574 q = 1) : d116366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d116366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d116366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d115574 q = 1) : d116369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d116369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28639 q ha hb
    | true =>
      simp only [d13694, d116369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d115574 q = 1) : d116370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d116370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d116370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d115574 q = 1) : d116371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d116371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d116371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d115574 q = 1) : d116372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d116372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d116372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d115574 q = 1) : d116373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d116373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d116373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13699 q = 1) (hb : d115574 q = 1) : d116374 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13699, d116374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13699, d116374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28646 (p : Pattern) (ha : d13744 p = 1) (hb : d115574 p = 1) : d116384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d115574 q = 1) : d116326 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28634 q ha hb
    | true =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d115574 q = 1) : d116327 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d115574 q = 1) : d116381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d116381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d116381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d115574 q = 1) : d116382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d116382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d116382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d115574 q = 1) : d116383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d116383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d116383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13744 q = 1) (hb : d115574 q = 1) : d116384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13744, d116384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13744, d116384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28647 (p : Pattern) (ha : d115485 p = 1) (hb : d115574 p = 1) : d116390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13657 q = 1) (hb : d115574 q = 1) : d13657 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13658 q = 1) (hb : d115574 q = 1) : d116352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d116352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28642 q ha hb
    | true =>
      simp only [d13658, d116352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13659 q = 1) (hb : d115574 q = 1) : d116353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d116353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d116353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13660 q = 1) (hb : d115574 q = 1) : d116354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d116354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13660, d116354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13661 q = 1) (hb : d115574 q = 1) : d116355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d116355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d116355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d115574 q = 1) : d13667 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13668 q = 1) (hb : d115574 q = 1) : d116359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d116359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28643 q ha hb
    | true =>
      simp only [d13668, d116359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13669 q = 1) (hb : d115574 q = 1) : d116360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d116360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d116360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13670 q = 1) (hb : d115574 q = 1) : d116361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d116361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13670, d116361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13704 q = 1) (hb : d115574 q = 1) : d116379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d116379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28645 q ha hb
    | true =>
      simp only [d13704, d116379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28640 q ha hb
  have h11 (q : Pattern) (ha : d115481 q = 1) (hb : d115574 q = 1) : d116380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d116380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115481, d116380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13745 q = 1) (hb : d115574 q = 1) : d116385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d116385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28646 q ha hb
    | true =>
      simp only [d13745, d116385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13746 q = 1) (hb : d115574 q = 1) : d116386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d116386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13746, d116386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115482 q = 1) (hb : d115574 q = 1) : d116387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d116387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115482, d116387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115483 q = 1) (hb : d115574 q = 1) : d116388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d116388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115483, d116388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115484 q = 1) (hb : d115574 q = 1) : d116389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d116389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115484, d116389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115485 q = 1) (hb : d115574 q = 1) : d116390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d116390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115485, d116390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro28648 (p : Pattern) (ha : d13751 p = 1) (hb : d115574 p = 1) : d116391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d115574 q = 1) : d116326 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28634 q ha hb
    | true =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d115574 q = 1) : d116327 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d115574 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d115574 q = 1) : d116328 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13628 q = 1) (hb : d115574 q = 1) : d116329 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13628, d116329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13628, d116329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13654 q = 1) (hb : d115574 q = 1) : d116350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13654, d116350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13654, d116350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13751 q = 1) (hb : d115574 q = 1) : d116391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13751, d116391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13751, d116391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28649 (p : Pattern) (ha : d13757 p = 1) (hb : d115574 p = 1) : d116396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d115574 q = 1) : d116326 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28634 q ha hb
    | true =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d115574 q = 1) : d116327 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d115574 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13627 q = 1) (hb : d115574 q = 1) : d116328 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13627, d116328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13662 q = 1) (hb : d115574 q = 1) : d116356 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13662, d116356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13662, d116356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13663 q = 1) (hb : d115574 q = 1) : d116357 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13663, d116357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13663, d116357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13757 q = 1) (hb : d115574 q = 1) : d116396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13757, d116396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13757, d116396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28650 (p : Pattern) (ha : d13762 p = 1) (hb : d115574 p = 1) : d116400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13690 q = 1) (hb : d115574 q = 1) : d116365 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13690, d116365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28644 q ha hb
    | true =>
      simp only [d13690, d116365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13691 q = 1) (hb : d115574 q = 1) : d116366 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13691, d116366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13691, d116366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13694 q = 1) (hb : d115574 q = 1) : d116369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d116369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28639 q ha hb
    | true =>
      simp only [d13694, d116369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13695 q = 1) (hb : d115574 q = 1) : d116370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d116370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d116370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13696 q = 1) (hb : d115574 q = 1) : d116371 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13696, d116371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13696, d116371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13697 q = 1) (hb : d115574 q = 1) : d116372 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13697, d116372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13697, d116372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13698 q = 1) (hb : d115574 q = 1) : d116373 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13698, d116373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13698, d116373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13762 q = 1) (hb : d115574 q = 1) : d116400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13762, d116400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13762, d116400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28651 (p : Pattern) (ha : d13763 p = 1) (hb : d115574 p = 1) : d116401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13694 q = 1) (hb : d115574 q = 1) : d116369 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13694, d116369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28639 q ha hb
    | true =>
      simp only [d13694, d116369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13695 q = 1) (hb : d115574 q = 1) : d116370 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13695, d116370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13695, d116370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13626 q = 1) (hb : d115574 q = 1) : d13626 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13700 q = 1) (hb : d115574 q = 1) : d116375 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13700, d116375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13700, d116375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13701 q = 1) (hb : d115574 q = 1) : d116376 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13701, d116376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13701, d116376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13702 q = 1) (hb : d115574 q = 1) : d116377 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13702, d116377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13702, d116377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13763 q = 1) (hb : d115574 q = 1) : d116401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13763, d116401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13763, d116401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28652 (p : Pattern) (ha : d13769 p = 1) (hb : d115574 p = 1) : d116404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13621 q = 1) (hb : d115574 q = 1) : d116326 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28634 q ha hb
    | true =>
      simp only [d13621, d116326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13622 q = 1) (hb : d115574 q = 1) : d116327 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13622, d116327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13741 q = 1) (hb : d115574 q = 1) : d116381 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13741, d116381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13741, d116381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13742 q = 1) (hb : d115574 q = 1) : d116382 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13742, d116382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13742, d116382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13743 q = 1) (hb : d115574 q = 1) : d116383 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13743, d116383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13743, d116383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13769 q = 1) (hb : d115574 q = 1) : d116404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13769, d116404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13769, d116404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28653 (p : Pattern) (ha : d115490 p = 1) (hb : d115574 p = 1) : d116410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13657 q = 1) (hb : d115574 q = 1) : d13657 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13658 q = 1) (hb : d115574 q = 1) : d116352 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13658, d116352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28642 q ha hb
    | true =>
      simp only [d13658, d116352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13659 q = 1) (hb : d115574 q = 1) : d116353 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13659, d116353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13659, d116353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13660 q = 1) (hb : d115574 q = 1) : d116354 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13660, d116354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13660, d116354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13661 q = 1) (hb : d115574 q = 1) : d116355 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13661, d116355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13661, d116355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13667 q = 1) (hb : d115574 q = 1) : d13667 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13668 q = 1) (hb : d115574 q = 1) : d116359 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13668, d116359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28643 q ha hb
    | true =>
      simp only [d13668, d116359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13669 q = 1) (hb : d115574 q = 1) : d116360 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13669, d116360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13669, d116360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13670 q = 1) (hb : d115574 q = 1) : d116361 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13670, d116361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13670, d116361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d13704 q = 1) (hb : d115574 q = 1) : d116379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13704, d116379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28645 q ha hb
    | true =>
      simp only [d13704, d116379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28640 q ha hb
  have h11 (q : Pattern) (ha : d115481 q = 1) (hb : d115574 q = 1) : d116380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d116380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115481, d116380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d13745 q = 1) (hb : d115574 q = 1) : d116385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13745, d116385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28646 q ha hb
    | true =>
      simp only [d13745, d116385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13746 q = 1) (hb : d115574 q = 1) : d116386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13746, d116386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d13746, d116386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d115482 q = 1) (hb : d115574 q = 1) : d116387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d116387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115482, d116387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115483 q = 1) (hb : d115574 q = 1) : d116388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d116388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115483, d116388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115484 q = 1) (hb : d115574 q = 1) : d116389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d116389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115484, d116389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d13752 q = 1) (hb : d115574 q = 1) : d13752 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d13753 q = 1) (hb : d115574 q = 1) : d116392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13753, d116392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28648 q ha hb
    | true =>
      simp only [d13753, d116392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d13754 q = 1) (hb : d115574 q = 1) : d116393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13754, d116393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13754, d116393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d13755 q = 1) (hb : d115574 q = 1) : d116394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13755, d116394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d13755, d116394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d13756 q = 1) (hb : d115574 q = 1) : d116395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13756, d116395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13756, d116395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d13758 q = 1) (hb : d115574 q = 1) : d13758 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d13759 q = 1) (hb : d115574 q = 1) : d116397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13759, d116397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28649 q ha hb
    | true =>
      simp only [d13759, d116397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d13760 q = 1) (hb : d115574 q = 1) : d116398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13760, d116398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13760, d116398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d13761 q = 1) (hb : d115574 q = 1) : d116399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13761, d116399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d13761, d116399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d13764 q = 1) (hb : d115574 q = 1) : d116402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d116402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28650 q ha hb
    | true =>
      simp only [d13764, d116402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28651 q ha hb
  have h27 (q : Pattern) (ha : d115486 q = 1) (hb : d115574 q = 1) : d116403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d116403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d115486, d116403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d13770 q = 1) (hb : d115574 q = 1) : d116405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d116405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28652 q ha hb
    | true =>
      simp only [d13770, d116405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d13771 q = 1) (hb : d115574 q = 1) : d116406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d116406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d13771, d116406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d115487 q = 1) (hb : d115574 q = 1) : d116407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d116407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d115487, d116407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d115488 q = 1) (hb : d115574 q = 1) : d116408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d116408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d115488, d116408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d115489 q = 1) (hb : d115574 q = 1) : d116409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d116409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115489, d116409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d115490 q = 1) (hb : d115574 q = 1) : d116410 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d116410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115490, d116410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro28654 (p : Pattern) (ha : d115497 p = 1) (hb : d115574 p = 1) : d116424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13764 q = 1) (hb : d115574 q = 1) : d116402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13764, d116402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28650 q ha hb
    | true =>
      simp only [d13764, d116402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28651 q ha hb
  have h2 (q : Pattern) (ha : d115486 q = 1) (hb : d115574 q = 1) : d116403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d116403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115486, d116403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13770 q = 1) (hb : d115574 q = 1) : d116405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13770, d116405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28652 q ha hb
    | true =>
      simp only [d13770, d116405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13771 q = 1) (hb : d115574 q = 1) : d116406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13771, d116406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13771, d116406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115487 q = 1) (hb : d115574 q = 1) : d116407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d116407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115487, d116407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115495 q = 1) (hb : d115574 q = 1) : d116422 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d116422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115495, d116422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115496 q = 1) (hb : d115574 q = 1) : d116423 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d116423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115496, d116423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115497 q = 1) (hb : d115574 q = 1) : d116424 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d116424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115497, d116424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28655 (p : Pattern) (ha : d13832 p = 1) (hb : d115574 p = 1) : d116433 p = 1 := by
  have h0 (q : Pattern) (ha : d13812 q = 1) (hb : d94753 q = 1) : d13812 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13825 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13826 q = 1) (hb : d115574 q = 1) : d116430 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13826, d115574, d116430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13826, d115574, d116430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13829 q = 1) (hb : d94753 q = 1) : d13829 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d6651 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d13830 q = 1) (hb : d115574 q = 1) : d116431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d115574, d116431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13830, d115574, d116431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d13831 q = 1) (hb : d115574 q = 1) : d116432 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13831, d116432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13831, d116432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13832 q = 1) (hb : d115574 q = 1) : d116433 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13832, d116433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13832, d116433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28656 (p : Pattern) (ha : d13836 p = 1) (hb : d115574 p = 1) : d116437 p = 1 := by
  have h0 (q : Pattern) (ha : d13829 q = 1) (hb : d94753 q = 1) : d13829 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13830 q = 1) (hb : d115574 q = 1) : d116431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d115574, d116431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13830, d115574, d116431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d6652 q = 1) (hb : d115574 q = 1) : d6652 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13835 q = 1) (hb : d115574 q = 1) : d116436 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13835, d116436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13835, d116436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13836 q = 1) (hb : d115574 q = 1) : d116437 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13836, d116437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13836, d116437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28657 (p : Pattern) (ha : d13842 p = 1) (hb : d115574 p = 1) : d116443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13833 q = 1) (hb : d115574 q = 1) : d116434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13833, d116434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28655 q ha hb
    | true =>
      simp only [d13833, d116434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13834 q = 1) (hb : d115574 q = 1) : d116435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13834, d116435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13834, d116435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13837 q = 1) (hb : d115574 q = 1) : d116438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d116438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28656 q ha hb
    | true =>
      simp only [d13837, d116438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13838 q = 1) (hb : d115574 q = 1) : d116439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d116439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d116439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13839 q = 1) (hb : d115574 q = 1) : d116440 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13839, d116440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13839, d116440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13840 q = 1) (hb : d115574 q = 1) : d116441 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13840, d116441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13840, d116441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13841 q = 1) (hb : d115574 q = 1) : d116442 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13841, d116442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13841, d116442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13842 q = 1) (hb : d115574 q = 1) : d116443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13842, d116443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13842, d116443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro28658 (p : Pattern) (ha : d13855 p = 1) (hb : d115574 p = 1) : d116447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13837 q = 1) (hb : d115574 q = 1) : d116438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13837, d116438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28656 q ha hb
    | true =>
      simp only [d13837, d116438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13838 q = 1) (hb : d115574 q = 1) : d116439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13838, d116439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13838, d116439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13851 q = 1) (hb : d115574 q = 1) : d13851 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13852 q = 1) (hb : d115574 q = 1) : d116444 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13852, d116444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13852, d116444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13853 q = 1) (hb : d115574 q = 1) : d116445 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13853, d116445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13853, d116445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13854 q = 1) (hb : d115574 q = 1) : d116446 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13854, d116446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13854, d116446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13855 q = 1) (hb : d115574 q = 1) : d116447 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13855, d116447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13855, d116447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro28659 (p : Pattern) (ha : d13896 p = 1) (hb : d115574 p = 1) : d116451 p = 1 := by
  have h0 (q : Pattern) (ha : d13829 q = 1) (hb : d94753 q = 1) : d13829 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d6651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13830 q = 1) (hb : d115574 q = 1) : d116431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d13830, d115574, d116431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13830, d115574, d116431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d13847 q = 1) (hb : d115574 q = 1) : d13847 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d13895 q = 1) (hb : d115574 q = 1) : d116450 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d13895, d116450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13895, d116450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d13896 q = 1) (hb : d115574 q = 1) : d116451 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d13896, d116451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13896, d116451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28660 (p : Pattern) (ha : d13902 p = 1) (hb : d115574 p = 1) : d116457 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d115574 q = 1) : d116452 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d116452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28659 q ha hb
    | true =>
      simp only [d13897, d116452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d115574 q = 1) : d116453 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d116453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d116453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13899 q = 1) (hb : d115574 q = 1) : d116454 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d13899, d116454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13899, d116454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13900 q = 1) (hb : d115574 q = 1) : d116455 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d13900, d116455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13900, d116455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13901 q = 1) (hb : d115574 q = 1) : d116456 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d13901, d116456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13901, d116456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13902 q = 1) (hb : d115574 q = 1) : d116457 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d13902, d116457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13902, d116457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28661 (p : Pattern) (ha : d115507 p = 1) (hb : d115574 p = 1) : d116463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13856 q = 1) (hb : d115574 q = 1) : d116448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13856, d116448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28657 q ha hb
    | true =>
      simp only [d13856, d116448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28658 q ha hb
  have h2 (q : Pattern) (ha : d115503 q = 1) (hb : d115574 q = 1) : d116449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d116449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115503, d116449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13903 q = 1) (hb : d115574 q = 1) : d116458 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13903, d116458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28660 q ha hb
    | true =>
      simp only [d13903, d116458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13904 q = 1) (hb : d115574 q = 1) : d116459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13904, d116459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13904, d116459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d115574 q = 1) : d116460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d116460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115504, d116460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d115574 q = 1) : d116461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d116461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d116461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d115574 q = 1) : d116462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d116462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d116462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d115574 q = 1) : d116463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d116463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d116463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28662 (p : Pattern) (ha : d115513 p = 1) (hb : d115574 p = 1) : d116469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13641 q = 1) (hb : d115574 q = 1) : d116338 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13641, d116338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13641, d116338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28636 q ha hb
  have h2 (q : Pattern) (ha : d13642 q = 1) (hb : d115574 q = 1) : d116339 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13642, d116339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13642, d116339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13651 q = 1) (hb : d115574 q = 1) : d116347 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d116347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28636 q ha hb
    | true =>
      simp only [d13651, d116347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28638 q ha hb
  have h4 (q : Pattern) (ha : d13652 q = 1) (hb : d115574 q = 1) : d116348 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d116348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13652, d116348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13653 q = 1) (hb : d115574 q = 1) : d116349 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d13653, d116349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13653, d116349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115491 q = 1) (hb : d115574 q = 1) : d116411 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d116411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28647 q ha hb
    | true =>
      simp only [d115491, d116411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28653 q ha hb
  have h7 (q : Pattern) (ha : d13793 q = 1) (hb : d115574 q = 1) : d13793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13794 q = 1) (hb : d115574 q = 1) : d116418 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13794, d116418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28641 q ha hb
    | true =>
      simp only [d13794, d116418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115492 q = 1) (hb : d115574 q = 1) : d116419 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d116419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115492, d116419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115493 q = 1) (hb : d115574 q = 1) : d116420 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d116420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115493, d116420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d115494 q = 1) (hb : d115574 q = 1) : d116421 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d116421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115494, d116421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115498 q = 1) (hb : d115574 q = 1) : d116425 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d116425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115498, d116425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28654 q ha hb
  have h13 (q : Pattern) (ha : d13803 q = 1) (hb : d115574 q = 1) : d13803 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d115499 q = 1) (hb : d115574 q = 1) : d116426 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d116426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115499, d116426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115500 q = 1) (hb : d115574 q = 1) : d116427 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d116427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d115500, d116427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d115501 q = 1) (hb : d115574 q = 1) : d116428 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d116428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115501, d116428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d115502 q = 1) (hb : d115574 q = 1) : d116429 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d116429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d115502, d116429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115508 q = 1) (hb : d115574 q = 1) : d116464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d116464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115508, d116464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28661 q ha hb
  have h19 (q : Pattern) (ha : d13920 q = 1) (hb : d115574 q = 1) : d13920 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d115509 q = 1) (hb : d115574 q = 1) : d116465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d116465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d115509, d116465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d115510 q = 1) (hb : d115574 q = 1) : d116466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d116466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d115510, d116466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d115511 q = 1) (hb : d115574 q = 1) : d116467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d116467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d115511, d116467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d115512 q = 1) (hb : d115574 q = 1) : d116468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d116468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d115512, d116468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d115513 q = 1) (hb : d115574 q = 1) : d116469 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d116469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115513, d116469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro28663 (p : Pattern) (ha : d115519 p = 1) (hb : d115574 p = 1) : d116475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d115574 q = 1) : d116470 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d116470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d116470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28662 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d115574 q = 1) : d116471 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d116471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d116471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d115574 q = 1) : d116472 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d116472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d116472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d115574 q = 1) : d116473 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d116473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d116473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d115574 q = 1) : d116474 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d116474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d116474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d115574 q = 1) : d116475 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d116475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d116475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28664 (p : Pattern) (ha : d115525 p = 1) (hb : d115574 p = 1) : d116481 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d115574 q = 1) : d115872 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d115872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28521 q ha hb
    | true =>
      simp only [d115354, d115872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28547 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d115574 q = 1) : d116008 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d116008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d116008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28573 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d115574 q = 1) : d116009 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d116009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d116009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d115574 q = 1) : d116163 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d116163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d116163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28603 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d115574 q = 1) : d116164 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d116164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d116164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d115574 q = 1) : d116165 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d116165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d116165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d115574 q = 1) : d116319 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d116319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d116319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28633 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d115574 q = 1) : d116320 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d116320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d116320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d115574 q = 1) : d116321 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d116321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d116321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d115574 q = 1) : d116322 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d116322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d116322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d115574 q = 1) : d116476 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d116476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d116476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28663 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d115574 q = 1) : d116477 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d116477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d116477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d115574 q = 1) : d116478 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d116478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d116478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d115574 q = 1) : d116479 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d116479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d116479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d115574 q = 1) : d116480 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d116480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d116480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d115574 q = 1) : d116481 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d116481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d116481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro28665 (p : Pattern) (ha : d115531 p = 1) (hb : d115574 p = 1) : d116487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d115574 q = 1) : d116482 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d116482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28664 q ha hb
    | true =>
      simp only [d115526, d116482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d115574 q = 1) : d116483 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d116483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d116483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d115574 q = 1) : d116484 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d116484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d116484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d115574 q = 1) : d116485 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d116485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d116485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d115574 q = 1) : d116486 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d116486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d116486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d115574 q = 1) : d116487 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d116487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d116487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28666 (p : Pattern) (ha : d115537 p = 1) (hb : d115574 p = 1) : d116493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d115574 q = 1) : d116488 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d116488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28665 q ha hb
    | true =>
      simp only [d115532, d116488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d115574 q = 1) : d116489 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d116489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d116489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d115574 q = 1) : d116490 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d116490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d116490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d115574 q = 1) : d116491 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d116491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d116491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d115574 q = 1) : d116492 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d116492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d116492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d115574 q = 1) : d116493 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d116493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d116493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28667 (p : Pattern) (ha : d115543 p = 1) (hb : d115574 p = 1) : d116499 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d115574 q = 1) : d116494 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d116494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28666 q ha hb
    | true =>
      simp only [d115538, d116494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d115574 q = 1) : d116495 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d116495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d116495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d115574 q = 1) : d116496 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d116496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d116496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d115574 q = 1) : d116497 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d116497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d116497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d115574 q = 1) : d116498 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d116498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d116498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d115574 q = 1) : d116499 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d116499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d116499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28668 (p : Pattern) (ha : d115549 p = 1) (hb : d115574 p = 1) : d116505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d115574 q = 1) : d116500 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d116500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28667 q ha hb
    | true =>
      simp only [d115544, d116500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d115574 q = 1) : d116501 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d116501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d116501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115546 q = 1) (hb : d115574 q = 1) : d116502 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d116502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d116502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115547 q = 1) (hb : d115574 q = 1) : d116503 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d116503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d116503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115548 q = 1) (hb : d115574 q = 1) : d116504 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d116504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d116504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115549 q = 1) (hb : d115574 q = 1) : d116505 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d116505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d116505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28669 (p : Pattern) (ha : d115555 p = 1) (hb : d115574 p = 1) : d116511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d115574 q = 1) : d116506 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d116506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28668 q ha hb
    | true =>
      simp only [d115550, d116506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d115574 q = 1) : d116507 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d116507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d116507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d115574 q = 1) : d116508 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d116508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d116508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d115574 q = 1) : d116509 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d116509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d116509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d115574 q = 1) : d116510 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d116510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d116510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d115574 q = 1) : d116511 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d116511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d116511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28670 (p : Pattern) (ha : d115561 p = 1) (hb : d115574 p = 1) : d116517 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d115574 q = 1) : d116512 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d116512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28669 q ha hb
    | true =>
      simp only [d115556, d116512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d115574 q = 1) : d116513 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d116513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d116513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d115574 q = 1) : d116514 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d116514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d116514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d115574 q = 1) : d116515 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d116515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d116515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d115574 q = 1) : d116516 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d116516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d116516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d115574 q = 1) : d116517 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d116517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d116517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28671 (p : Pattern) (ha : d115567 p = 1) (hb : d115574 p = 1) : d116523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d115574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d115574 q = 1) : d116518 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d116518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28670 q ha hb
    | true =>
      simp only [d115562, d116518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d115574 q = 1) : d116519 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d116519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d116519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d115574 q = 1) : d116520 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d116520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d116520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d115574 q = 1) : d116521 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d116521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d116521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d115574 q = 1) : d116522 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d116522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d116522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d115574 q = 1) : d116523 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d116523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d116523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28672 (p : Pattern) (ha : d81527 p = 1) (hb : d115576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
    | true =>
      simp only [d4819, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4822 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4822, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d81526 q = 1) (hb : d115575 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81526, d115575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81526, d115575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81527 q = 1) (hb : d115576 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81527, d115576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81527, d115576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro28673 (p : Pattern) (ha : d92321 p = 1) (hb : d115582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d115579 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d115580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92320 q = 1) (hb : d115581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92320, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92320, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92321 q = 1) (hb : d115582 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92321, d115582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92321, d115582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28674 (p : Pattern) (ha : d92327 p = 1) (hb : d115588 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d115583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28673 q ha hb
    | true =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d115584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d115585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d115586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d115587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92327 q = 1) (hb : d115588 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92327, d115588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92327, d115588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro28675 (p : Pattern) (ha : d92328 p = 1) (hb : d115589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d115579 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d115580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92320 q = 1) (hb : d115581 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92320, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92320, d115581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92328 q = 1) (hb : d115589 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92328, d115589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92328, d115589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28676 (p : Pattern) (ha : d92334 p = 1) (hb : d115595 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d92322 q = 1) (hb : d115583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28673 q ha hb
    | true =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92323 q = 1) (hb : d115584 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92323, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92323, d115584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d92324 q = 1) (hb : d115585 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92324, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92324, d115585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92325 q = 1) (hb : d115586 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92325, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d92325, d115586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92326 q = 1) (hb : d115587 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92326, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92326, d115587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d92329 q = 1) (hb : d115590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28675 q ha hb
    | true =>
      simp only [d92329, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92330 q = 1) (hb : d115591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92330, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d92331 q = 1) (hb : d115592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92331, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d92332 q = 1) (hb : d115593 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92332, d115593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d92332, d115593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92333 q = 1) (hb : d115594 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92333, d115594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d92333, d115594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92334 q = 1) (hb : d115595 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92334, d115595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92334, d115595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro28677 (p : Pattern) (ha : d92341 p = 1) (hb : d115602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92329 q = 1) (hb : d115590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28675 q ha hb
    | true =>
      simp only [d92329, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92330 q = 1) (hb : d115591 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92330, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92330, d115591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d92331 q = 1) (hb : d115592 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92331, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92331, d115592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92339 q = 1) (hb : d115600 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92339, d115600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92339, d115600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92340 q = 1) (hb : d115601 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92340, d115601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92340, d115601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92341 q = 1) (hb : d115602 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92341, d115602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92341, d115602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28678 (p : Pattern) (ha : d81560 p = 1) (hb : d115609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d6079, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6082 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6082, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d81559 q = 1) (hb : d115608 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81559, d115608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d81559, d115608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81560 q = 1) (hb : d115609 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81560, d115609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81560, d115609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro28679 (p : Pattern) (ha : d92350 p = 1) (hb : d115615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81561 q = 1) (hb : d115610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81561, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28678 q ha hb
    | true =>
      simp only [d81561, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81562 q = 1) (hb : d115611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81562, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81562, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92347 q = 1) (hb : d115612 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92347, d115612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92347, d115612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92348 q = 1) (hb : d115613 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92348, d115613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92348, d115613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92349 q = 1) (hb : d115614 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92349, d115614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92349, d115614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92350 q = 1) (hb : d115615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92350, d115615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92350, d115615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28680 (p : Pattern) (ha : d92356 p = 1) (hb : d115621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92351 q = 1) (hb : d115616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92351, d115616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28679 q ha hb
    | true =>
      simp only [d92351, d115616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92352 q = 1) (hb : d115617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92352, d115617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92352, d115617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d92353 q = 1) (hb : d115618 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92353, d115618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92353, d115618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d92354 q = 1) (hb : d115619 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92354, d115619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92354, d115619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92355 q = 1) (hb : d115620 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92355, d115620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92355, d115620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92356 q = 1) (hb : d115621 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92356, d115621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92356, d115621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28681 (p : Pattern) (ha : d92362 p = 1) (hb : d115627 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d92335 q = 1) (hb : d115596 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92335, d115596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28674 q ha hb
    | true =>
      simp only [d92335, d115596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28676 q ha hb
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
  have h8 (q : Pattern) (ha : d92336 q = 1) (hb : d115597 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92336, d115597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92336, d115597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d92337 q = 1) (hb : d115598 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92337, d115598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92337, d115598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92338 q = 1) (hb : d115599 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92338, d115599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d92338, d115599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92342 q = 1) (hb : d115603 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92342, d115603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92342, d115603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28677 q ha hb
  have h12 (q : Pattern) (ha : d92343 q = 1) (hb : d115604 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92343, d115604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92343, d115604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92344 q = 1) (hb : d115605 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92344, d115605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d92344, d115605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92345 q = 1) (hb : d115606 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92345, d115606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92345, d115606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92346 q = 1) (hb : d115607 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92346, d115607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92346, d115607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92357 q = 1) (hb : d115622 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92357, d115622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92357, d115622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28680 q ha hb
  have h17 (q : Pattern) (ha : d92358 q = 1) (hb : d115623 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92358, d115623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92358, d115623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d92359 q = 1) (hb : d115624 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92359, d115624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92359, d115624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92360 q = 1) (hb : d115625 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92360, d115625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d92360, d115625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d92361 q = 1) (hb : d115626 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92361, d115626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92361, d115626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92362 q = 1) (hb : d115627 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92362, d115627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92362, d115627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro28682 (p : Pattern) (ha : d92372 p = 1) (hb : d115637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d115583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28673 q ha hb
    | true =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d115633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d115634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d115635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d115636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92372 q = 1) (hb : d115637 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92372, d115637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92372, d115637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28683 (p : Pattern) (ha : d92379 p = 1) (hb : d115644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d115583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28673 q ha hb
    | true =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d115633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d115634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d115635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d115636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92329 q = 1) (hb : d115590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92329, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28675 q ha hb
    | true =>
      simp only [d92329, d115590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d92375 q = 1) (hb : d115640 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92375, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92375, d115640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92376 q = 1) (hb : d115641 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92376, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92376, d115641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92377 q = 1) (hb : d115642 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92377, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92377, d115642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92378 q = 1) (hb : d115643 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92378, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92378, d115643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92379 q = 1) (hb : d115644 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92379, d115644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92379, d115644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28684 (p : Pattern) (ha : d92384 p = 1) (hb : d115649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d115579 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d115580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92383 q = 1) (hb : d115648 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92384 q = 1) (hb : d115649 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92384, d115649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92384, d115649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28685 (p : Pattern) (ha : d92391 p = 1) (hb : d115656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d115579 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92389 q = 1) (hb : d115654 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92390 q = 1) (hb : d115655 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92390, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92391 q = 1) (hb : d115656 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92391, d115656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92391, d115656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28686 (p : Pattern) (ha : d92396 p = 1) (hb : d115662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q ha hb
    | true =>
      simp only [d12313, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81585 q = 1) (hb : d115660 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81585, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81585, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d4819 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
    | true =>
      simp only [d4819, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h6 (q : Pattern) (ha : d4820 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4821 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4822 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4822, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d92395 q = 1) (hb : d115661 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92395, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92395, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92396 q = 1) (hb : d115662 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92396, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92396, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro28687 (p : Pattern) (ha : d92402 p = 1) (hb : d115668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92399 q = 1) (hb : d115665 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92399, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92399, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92400 q = 1) (hb : d115666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92400, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92400, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92401 q = 1) (hb : d115667 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92401, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92401, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92402 q = 1) (hb : d115668 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92402, d115668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92402, d115668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28688 (p : Pattern) (ha : d92408 p = 1) (hb : d115674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92405 q = 1) (hb : d115671 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92405, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92405, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92406 q = 1) (hb : d115672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92406, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92406, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92407 q = 1) (hb : d115673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92407, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92407, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92408 q = 1) (hb : d115674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92408, d115674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92408, d115674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28689 (p : Pattern) (ha : d92414 p = 1) (hb : d115680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d115650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28684 q ha hb
    | true =>
      simp only [d92385, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d115651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d115652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d115653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d115657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28685 q ha hb
    | true =>
      simp only [d92392, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d115658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d115659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d115669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28687 q ha hb
    | true =>
      simp only [d92403, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28673 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d115670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92409 q = 1) (hb : d115675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92409, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28688 q ha hb
    | true =>
      simp only [d92409, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92410 q = 1) (hb : d115676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92410, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92410, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d115677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d115678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d115679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92414 q = 1) (hb : d115680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92414, d115680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92414, d115680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro28690 (p : Pattern) (ha : d92415 p = 1) (hb : d115681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d115579 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92319 q = 1) (hb : d115580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92319, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92319, d115580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92383 q = 1) (hb : d115648 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92383, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92383, d115648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92415 q = 1) (hb : d115681 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92415, d115681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92415, d115681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28691 (p : Pattern) (ha : d92420 p = 1) (hb : d115686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d92318 q = 1) (hb : d115579 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92318, d115579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92389 q = 1) (hb : d115654 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92389, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92389, d115654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92390 q = 1) (hb : d115655 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92390, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92390, d115655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92420 q = 1) (hb : d115686 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92420, d115686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92420, d115686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28692 (p : Pattern) (ha : d92424 p = 1) (hb : d115690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92399 q = 1) (hb : d115665 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92399, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92399, d115665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92400 q = 1) (hb : d115666 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92400, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92400, d115666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92401 q = 1) (hb : d115667 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92401, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92401, d115667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92424 q = 1) (hb : d115690 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92424, d115690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92424, d115690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28693 (p : Pattern) (ha : d92427 p = 1) (hb : d115693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81528 q = 1) (hb : d115577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28672 q ha hb
    | true =>
      simp only [d81528, d115577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81529 q = 1) (hb : d115578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81529, d115578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92405 q = 1) (hb : d115671 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92405, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92405, d115671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92406 q = 1) (hb : d115672 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92406, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92406, d115672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92407 q = 1) (hb : d115673 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92407, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92407, d115673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92427 q = 1) (hb : d115693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92427, d115693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92427, d115693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28694 (p : Pattern) (ha : d92433 p = 1) (hb : d115699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92385 q = 1) (hb : d115650 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92385, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28684 q ha hb
    | true =>
      simp only [d92385, d115650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d92386 q = 1) (hb : d115651 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92386, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92386, d115651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92387 q = 1) (hb : d115652 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92387, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92387, d115652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92388 q = 1) (hb : d115653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92388, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92388, d115653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92392 q = 1) (hb : d115657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92392, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28685 q ha hb
    | true =>
      simp only [d92392, d115657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d92393 q = 1) (hb : d115658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92393, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92393, d115658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92394 q = 1) (hb : d115659 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92394, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92394, d115659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92403 q = 1) (hb : d115669 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92403, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28687 q ha hb
    | true =>
      simp only [d92403, d115669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28673 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92322 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92404 q = 1) (hb : d115670 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92404, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92404, d115670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92409 q = 1) (hb : d115675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92409, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28688 q ha hb
    | true =>
      simp only [d92409, d115675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92410 q = 1) (hb : d115676 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92410, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92410, d115676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92411 q = 1) (hb : d115677 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92411, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92411, d115677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92412 q = 1) (hb : d115678 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92412, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92412, d115678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92413 q = 1) (hb : d115679 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92413, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92413, d115679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92416 q = 1) (hb : d115682 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92416, d115682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28690 q ha hb
    | true =>
      simp only [d92416, d115682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d92417 q = 1) (hb : d115683 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92417, d115683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92417, d115683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92418 q = 1) (hb : d115684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92418, d115684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92418, d115684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92419 q = 1) (hb : d115685 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92419, d115685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92419, d115685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92421 q = 1) (hb : d115687 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92421, d115687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28691 q ha hb
    | true =>
      simp only [d92421, d115687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d92422 q = 1) (hb : d115688 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92422, d115688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92422, d115688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92423 q = 1) (hb : d115689 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92423, d115689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92423, d115689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92425 q = 1) (hb : d115691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28692 q ha hb
    | true =>
      simp only [d92425, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28675 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92426 q = 1) (hb : d115692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92426, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92428 q = 1) (hb : d115694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92428, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28693 q ha hb
    | true =>
      simp only [d92428, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92429 q = 1) (hb : d115695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92429, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92429, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92430 q = 1) (hb : d115696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92430, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92431 q = 1) (hb : d115697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92431, d115697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92431, d115697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92432 q = 1) (hb : d115698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92432, d115698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92432, d115698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92433 q = 1) (hb : d115699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92433, d115699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92433, d115699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro28695 (p : Pattern) (ha : d92435 p = 1) (hb : d115701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92322 q = 1) (hb : d115583 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28673 q ha hb
    | true =>
      simp only [d92322, d115583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d92368 q = 1) (hb : d115633 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92368, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92368, d115633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92369 q = 1) (hb : d115634 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92369, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92369, d115634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92370 q = 1) (hb : d115635 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92370, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92370, d115635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92371 q = 1) (hb : d115636 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92371, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92371, d115636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d92435 q = 1) (hb : d115701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92435, d115701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92435, d115701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro28696 (p : Pattern) (ha : d92442 p = 1) (hb : d115708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92425 q = 1) (hb : d115691 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92425, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28692 q ha hb
    | true =>
      simp only [d92425, d115691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28675 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92329 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92426 q = 1) (hb : d115692 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92426, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92426, d115692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92428 q = 1) (hb : d115694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92428, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28693 q ha hb
    | true =>
      simp only [d92428, d115694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92429 q = 1) (hb : d115695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92429, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92429, d115695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92430 q = 1) (hb : d115696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92430, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92430, d115696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92440 q = 1) (hb : d115706 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92440, d115706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92440, d115706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92441 q = 1) (hb : d115707 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92441, d115707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92441, d115707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92442 q = 1) (hb : d115708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92442, d115708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92442, d115708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28697 (p : Pattern) (ha : d92449 p = 1) (hb : d115716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q ha hb
    | true =>
      simp only [d12387, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81631 q = 1) (hb : d115714 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81631, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81631, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d6079 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d6079, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h6 (q : Pattern) (ha : d6080 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6081 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6082 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6082, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d92448 q = 1) (hb : d115715 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92448, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92448, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d92449 q = 1) (hb : d115716 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92449, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92449, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro28698 (p : Pattern) (ha : d92455 p = 1) (hb : d115722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92450 q = 1) (hb : d115717 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92450, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28697 q ha hb
    | true =>
      simp only [d92450, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92451 q = 1) (hb : d115718 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92451, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92451, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81561 q = 1) (hb : d115610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81561, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28678 q ha hb
    | true =>
      simp only [d81561, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81562 q = 1) (hb : d115611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81562, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81562, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92452 q = 1) (hb : d115719 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92452, d115719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92452, d115719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92453 q = 1) (hb : d115720 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92453, d115720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92453, d115720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92454 q = 1) (hb : d115721 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92454, d115721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92454, d115721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92455 q = 1) (hb : d115722 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92455, d115722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92455, d115722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28699 (p : Pattern) (ha : d92461 p = 1) (hb : d115728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81561 q = 1) (hb : d115610 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81561, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28678 q ha hb
    | true =>
      simp only [d81561, d115610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81562 q = 1) (hb : d115611 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81562, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81562, d115611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92458 q = 1) (hb : d115725 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92458, d115725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92458, d115725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92459 q = 1) (hb : d115726 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92459, d115726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92459, d115726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92460 q = 1) (hb : d115727 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92460, d115727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92460, d115727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92461 q = 1) (hb : d115728 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92461, d115728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92461, d115728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28700 (p : Pattern) (ha : d92467 p = 1) (hb : d115734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92456 q = 1) (hb : d115723 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92456, d115723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28698 q ha hb
    | true =>
      simp only [d92456, d115723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28679 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92457 q = 1) (hb : d115724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92457, d115724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92457, d115724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92462 q = 1) (hb : d115729 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92462, d115729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28699 q ha hb
    | true =>
      simp only [d92462, d115729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92463 q = 1) (hb : d115730 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92463, d115730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92463, d115730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92464 q = 1) (hb : d115731 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92464, d115731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92464, d115731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92465 q = 1) (hb : d115732 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92465, d115732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92465, d115732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92466 q = 1) (hb : d115733 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92466, d115733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92466, d115733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92467 q = 1) (hb : d115734 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92467, d115734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92467, d115734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28701 (p : Pattern) (ha : d92473 p = 1) (hb : d115740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92373 q = 1) (hb : d115638 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92373, d115638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92373, d115638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28682 q ha hb
  have h2 (q : Pattern) (ha : d92374 q = 1) (hb : d115639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92374, d115639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92374, d115639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92380 q = 1) (hb : d115645 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92380, d115645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28682 q ha hb
    | true =>
      simp only [d92380, d115645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28683 q ha hb
  have h4 (q : Pattern) (ha : d92381 q = 1) (hb : d115646 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92381, d115646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92381, d115646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92382 q = 1) (hb : d115647 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92382, d115647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92382, d115647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92434 q = 1) (hb : d115700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92434, d115700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28689 q ha hb
    | true =>
      simp only [d92434, d115700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28694 q ha hb
  have h7 (q : Pattern) (ha : d92436 q = 1) (hb : d115702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92436, d115702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28695 q ha hb
    | true =>
      simp only [d92436, d115702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d92437 q = 1) (hb : d115703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92437, d115703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92437, d115703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92438 q = 1) (hb : d115704 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92438, d115704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92438, d115704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92439 q = 1) (hb : d115705 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92439, d115705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92439, d115705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92443 q = 1) (hb : d115709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92443, d115709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92443, d115709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28696 q ha hb
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
  have h13 (q : Pattern) (ha : d92444 q = 1) (hb : d115710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92444, d115710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92444, d115710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92445 q = 1) (hb : d115711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92445, d115711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92445, d115711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92446 q = 1) (hb : d115712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92446, d115712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92446, d115712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92447 q = 1) (hb : d115713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92447, d115713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92447, d115713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92468 q = 1) (hb : d115735 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92468, d115735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92468, d115735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28700 q ha hb
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
  have h19 (q : Pattern) (ha : d92469 q = 1) (hb : d115736 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92469, d115736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92469, d115736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92470 q = 1) (hb : d115737 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92470, d115737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92470, d115737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92471 q = 1) (hb : d115738 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92471, d115738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92471, d115738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92472 q = 1) (hb : d115739 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92472, d115739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92472, d115739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92473 q = 1) (hb : d115740 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92473, d115740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92473, d115740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro28702 (p : Pattern) (ha : d92479 p = 1) (hb : d115746 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d92363 q = 1) (hb : d115628 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92363, d115628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92363, d115628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28681 q ha hb
  have h6 (q : Pattern) (ha : d92364 q = 1) (hb : d115629 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92364, d115629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92364, d115629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92365 q = 1) (hb : d115630 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92365, d115630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92365, d115630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92366 q = 1) (hb : d115631 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92366, d115631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92366, d115631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92367 q = 1) (hb : d115632 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92367, d115632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d92367, d115632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92474 q = 1) (hb : d115741 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92474, d115741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92474, d115741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28701 q ha hb
  have h11 (q : Pattern) (ha : d92475 q = 1) (hb : d115742 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92475, d115742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92475, d115742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d92476 q = 1) (hb : d115743 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92476, d115743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92476, d115743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92477 q = 1) (hb : d115744 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92477, d115744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92477, d115744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92478 q = 1) (hb : d115745 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92478, d115745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92478, d115745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92479 q = 1) (hb : d115746 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92479, d115746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92479, d115746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro28703 (p : Pattern) (ha : d12442 p = 1) (hb : d52228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4819 q = 1) (hb : d51996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
    | true =>
      simp only [d4819, d51996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h2 (q : Pattern) (ha : d4820 q = 1) (hb : d51997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d51997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4821 q = 1) (hb : d51998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d51998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4822 q = 1) (hb : d52222 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4822, d52222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12441 q = 1) (hb : d52227 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12441, d52227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12441, d52227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12442 q = 1) (hb : d52228 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12442, d52228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12442, d52228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28704 (p : Pattern) (ha : d12452 p = 1) (hb : d52238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d52237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12452 q = 1) (hb : d52238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12452, d52238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12452, d52238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28705 (p : Pattern) (ha : d12462 p = 1) (hb : d52248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12451 q = 1) (hb : d52237 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12451, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12451, d52237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12462 q = 1) (hb : d52248 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12462, d52248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12462, d52248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28706 (p : Pattern) (ha : d12580 p = 1) (hb : d52348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12569 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q ha hb
    | true =>
      simp only [d12569, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12570 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12571 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12571, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12572 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12573 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12575 q = 1) (hb : d52343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28705 q ha hb
    | true =>
      simp only [d12575, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12576 q = 1) (hb : d52344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12577 q = 1) (hb : d52345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12577, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12578 q = 1) (hb : d52346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12579 q = 1) (hb : d52347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12580 q = 1) (hb : d52348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12580, d52348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12580, d52348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28707 (p : Pattern) (ha : d12589 p = 1) (hb : d52357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12575 q = 1) (hb : d52343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12575, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28705 q ha hb
    | true =>
      simp only [d12575, d52343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12576 q = 1) (hb : d52344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12576, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12576, d52344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12577 q = 1) (hb : d52345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12577, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12577, d52345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12578 q = 1) (hb : d52346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12578, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12578, d52346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12579 q = 1) (hb : d52347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12579, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12579, d52347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12589 q = 1) (hb : d52357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12589, d52357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12589, d52357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28708 (p : Pattern) (ha : d12622 p = 1) (hb : d52387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6079 q = 1) (hb : d52050 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
    | true =>
      simp only [d6079, d52050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h2 (q : Pattern) (ha : d6080 q = 1) (hb : d52051 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d52051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6081 q = 1) (hb : d52052 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d52052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6082 q = 1) (hb : d52377 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d6082, d52377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12621 q = 1) (hb : d52386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12621, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12621, d52386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12622 q = 1) (hb : d52387 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12622, d52387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12622, d52387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28709 (p : Pattern) (ha : d12668 p = 1) (hb : d52398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12623 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28708 q ha hb
    | true =>
      simp only [d12623, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12624 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12665 q = 1) (hb : d52395 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12665, d52395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12665, d52395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12666 q = 1) (hb : d52396 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12666, d52396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12666, d52396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12667 q = 1) (hb : d52397 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12667, d52397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12667, d52397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12668 q = 1) (hb : d52398 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12668, d52398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12668, d52398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28710 (p : Pattern) (ha : d12674 p = 1) (hb : d52413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12669 q = 1) (hb : d52408 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12669, d52408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28709 q ha hb
    | true =>
      simp only [d12669, d52408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12670 q = 1) (hb : d52409 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12670, d52409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12670, d52409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12671 q = 1) (hb : d52410 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12671, d52410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12671, d52410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12672 q = 1) (hb : d52411 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12672, d52411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12672, d52411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12673 q = 1) (hb : d52412 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12673, d52412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12673, d52412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12674 q = 1) (hb : d52413 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12674, d52413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12674, d52413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28711 (p : Pattern) (ha : d92483 p = 1) (hb : d115750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d115747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d115748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92482 q = 1) (hb : d115749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92482, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92482, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92483 q = 1) (hb : d115750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92483, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92483, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28712 (p : Pattern) (ha : d92489 p = 1) (hb : d115756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92484 q = 1) (hb : d115751 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28711 q ha hb
    | true =>
      simp only [d92484, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h2 (q : Pattern) (ha : d92485 q = 1) (hb : d115752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92485, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92485, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92486 q = 1) (hb : d115753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92486, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92486, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92487 q = 1) (hb : d115754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92487, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92487, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92488 q = 1) (hb : d115755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92488, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92488, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92489 q = 1) (hb : d115756 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92489, d115756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92489, d115756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28713 (p : Pattern) (ha : d92492 p = 1) (hb : d115759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d115747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d115748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92482 q = 1) (hb : d115749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92482, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92482, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92492 q = 1) (hb : d115759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92492, d115759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92492, d115759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28714 (p : Pattern) (ha : d92498 p = 1) (hb : d115765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92484 q = 1) (hb : d115751 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92484, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28711 q ha hb
    | true =>
      simp only [d92484, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h2 (q : Pattern) (ha : d92485 q = 1) (hb : d115752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92485, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92485, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92486 q = 1) (hb : d115753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92486, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92486, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92487 q = 1) (hb : d115754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92487, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92487, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92488 q = 1) (hb : d115755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92488, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92488, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92493 q = 1) (hb : d115760 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92493, d115760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28713 q ha hb
    | true =>
      simp only [d92493, d115760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28705 q hb ha
  have h7 (q : Pattern) (ha : d92494 q = 1) (hb : d115761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92494, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92494, d115761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92495 q = 1) (hb : d115762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92495, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92495, d115762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92496 q = 1) (hb : d115763 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92496, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92496, d115763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92497 q = 1) (hb : d115764 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92497, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92497, d115764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92498 q = 1) (hb : d115765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92498, d115765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92498, d115765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28715 (p : Pattern) (ha : d12475 p = 1) (hb : d52261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d52260 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12475 q = 1) (hb : d52261 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12475, d52261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12475, d52261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28716 (p : Pattern) (ha : d12485 p = 1) (hb : d52271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d52269 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d52270 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12485 q = 1) (hb : d52271 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12485, d52271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12485, d52271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28717 (p : Pattern) (ha : d92503 p = 1) (hb : d115770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d115747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d115748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92502 q = 1) (hb : d115769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92502, d115769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92502, d115769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92503 q = 1) (hb : d115770 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92503, d115770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92503, d115770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28718 (p : Pattern) (ha : d92510 p = 1) (hb : d115777 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d115747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92508 q = 1) (hb : d115775 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92508, d115775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92508, d115775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92509 q = 1) (hb : d115776 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92509, d115776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92509, d115776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92510 q = 1) (hb : d115777 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92510, d115777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92510, d115777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28719 (p : Pattern) (ha : d81587 p = 1) (hb : d115662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12313 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q ha hb
    | true =>
      simp only [d12313, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
  have h2 (q : Pattern) (ha : d12314 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12315 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81585 q = 1) (hb : d115660 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81585, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81585, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d4819 q = 1) (hb : d68915 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q ha hb
    | true =>
      simp only [d4819, d68915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
  have h6 (q : Pattern) (ha : d4820 q = 1) (hb : d68916 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4820, d68916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4821 q = 1) (hb : d68917 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4821, d68917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4822 q = 1) (hb : d68918 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4822, d68918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4822, d68918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d81586 q = 1) (hb : d115661 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81586, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81586, d115661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81587 q = 1) (hb : d115662 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81587, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81587, d115662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro28720 (p : Pattern) (ha : d12489 p = 1) (hb : d52295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d52292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d52292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d52293 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d52293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d547 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d547, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d547, d52294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12489 q = 1) (hb : d52295 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12489, d52295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12489, d52295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28721 (p : Pattern) (ha : d92516 p = 1) (hb : d115783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12490 q = 1) (hb : d52296 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12490, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28720 q ha hb
    | true =>
      simp only [d12490, d52296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q ha hb
  have h2 (q : Pattern) (ha : d12491 q = 1) (hb : d52297 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12491, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12491, d52297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12492 q = 1) (hb : d52298 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12492, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12492, d52298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92514 q = 1) (hb : d115781 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92514, d115781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92514, d115781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d12313 q = 1) (hb : d52124 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12313, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22838 q ha hb
    | true =>
      simp only [d12313, d52124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10549 q ha hb
  have h6 (q : Pattern) (ha : d12314 q = 1) (hb : d52125 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12314, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12314, d52125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12315 q = 1) (hb : d52126 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12315, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12315, d52126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81585 q = 1) (hb : d115660 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81585, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81585, d115660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92515 q = 1) (hb : d115782 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92515, d115782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92515, d115782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92516 q = 1) (hb : d115783 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92516, d115783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92516, d115783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro28722 (p : Pattern) (ha : d92522 p = 1) (hb : d115789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92517 q = 1) (hb : d115784 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92517, d115784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28721 q ha hb
    | true =>
      simp only [d92517, d115784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92518 q = 1) (hb : d115785 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92518, d115785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92518, d115785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81588 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28719 q ha hb
    | true =>
      simp only [d81588, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81589 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92519 q = 1) (hb : d115786 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92519, d115786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92519, d115786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92520 q = 1) (hb : d115787 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92520, d115787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92520, d115787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92521 q = 1) (hb : d115788 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92521, d115788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92521, d115788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92522 q = 1) (hb : d115789 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92522, d115789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92522, d115789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28723 (p : Pattern) (ha : d92526 p = 1) (hb : d115750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81588 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28719 q ha hb
    | true =>
      simp only [d81588, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81589 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92523 q = 1) (hb : d115747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92523, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92523, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92524 q = 1) (hb : d115748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92524, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92524, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92525 q = 1) (hb : d115749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92525, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92525, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92526 q = 1) (hb : d115750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92526, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92526, d115750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro28724 (p : Pattern) (ha : d92532 p = 1) (hb : d115795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92529 q = 1) (hb : d115792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92529, d115792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92529, d115792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92530 q = 1) (hb : d115793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92530, d115793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92530, d115793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92531 q = 1) (hb : d115794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92531, d115794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92531, d115794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92532 q = 1) (hb : d115795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92532, d115795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92532, d115795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28725 (p : Pattern) (ha : d92538 p = 1) (hb : d115801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92504 q = 1) (hb : d115771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92504, d115771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28717 q ha hb
    | true =>
      simp only [d92504, d115771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28715 q hb ha
  have h2 (q : Pattern) (ha : d92505 q = 1) (hb : d115772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92505, d115772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92505, d115772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92506 q = 1) (hb : d115773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92506, d115773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92506, d115773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92507 q = 1) (hb : d115774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92507, d115774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92507, d115774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92511 q = 1) (hb : d115778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92511, d115778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28718 q ha hb
    | true =>
      simp only [d92511, d115778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28716 q hb ha
  have h6 (q : Pattern) (ha : d92512 q = 1) (hb : d115779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92512, d115779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92512, d115779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92513 q = 1) (hb : d115780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92513, d115780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92513, d115780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92527 q = 1) (hb : d115790 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92527, d115790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28722 q ha hb
    | true =>
      simp only [d92527, d115790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28723 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92484 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92528 q = 1) (hb : d115791 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d115791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92528, d115791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92533 q = 1) (hb : d115796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92533, d115796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28724 q ha hb
    | true =>
      simp only [d92533, d115796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92534 q = 1) (hb : d115797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92534, d115797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92534, d115797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92535 q = 1) (hb : d115798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d115798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92535, d115798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92536 q = 1) (hb : d115799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d115799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92536, d115799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92537 q = 1) (hb : d115800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d115800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92537, d115800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92538 q = 1) (hb : d115801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92538, d115801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92538, d115801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro28726 (p : Pattern) (ha : d12545 p = 1) (hb : d52317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12450 q = 1) (hb : d52236 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12450, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12450, d52236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12474 q = 1) (hb : d52260 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12474, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12474, d52260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12545 q = 1) (hb : d52317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12545, d52317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12545, d52317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28727 (p : Pattern) (ha : d12551 p = 1) (hb : d52323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12449 q = 1) (hb : d52235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12449, d52235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12483 q = 1) (hb : d52269 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12483, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12483, d52269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12484 q = 1) (hb : d52270 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12484, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12484, d52270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12551 q = 1) (hb : d52323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12551, d52323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12551, d52323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28728 (p : Pattern) (ha : d92539 p = 1) (hb : d115802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d115747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92481 q = 1) (hb : d115748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92481, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92481, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92502 q = 1) (hb : d115769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92502, d115769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92502, d115769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92539 q = 1) (hb : d115802 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92539, d115802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92539, d115802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28729 (p : Pattern) (ha : d92544 p = 1) (hb : d115807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92480 q = 1) (hb : d115747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92480, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92508 q = 1) (hb : d115775 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92508, d115775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92508, d115775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92509 q = 1) (hb : d115776 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92509, d115776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92509, d115776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92544 q = 1) (hb : d115807 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92544, d115807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92544, d115807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28730 (p : Pattern) (ha : d92548 p = 1) (hb : d115811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92517 q = 1) (hb : d115784 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92517, d115784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28721 q ha hb
    | true =>
      simp only [d92517, d115784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92518 q = 1) (hb : d115785 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92518, d115785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92518, d115785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81588 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28719 q ha hb
    | true =>
      simp only [d81588, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81589 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92519 q = 1) (hb : d115786 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92519, d115786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92519, d115786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92520 q = 1) (hb : d115787 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92520, d115787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92520, d115787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92521 q = 1) (hb : d115788 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92521, d115788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92521, d115788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92548 q = 1) (hb : d115811 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92548, d115811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92548, d115811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28731 (p : Pattern) (ha : d92549 p = 1) (hb : d115759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81588 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81588, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28719 q ha hb
    | true =>
      simp only [d81588, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81589 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81589, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81589, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12443 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28703 q ha hb
    | true =>
      simp only [d12443, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12444 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12444, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92523 q = 1) (hb : d115747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92523, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92523, d115747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92524 q = 1) (hb : d115748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92524, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92524, d115748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92525 q = 1) (hb : d115749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92525, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92525, d115749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92549 q = 1) (hb : d115759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92549, d115759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92549, d115759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28732 (p : Pattern) (ha : d92552 p = 1) (hb : d115814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92397 q = 1) (hb : d115663 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28686 q ha hb
    | true =>
      simp only [d92397, d115663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92398 q = 1) (hb : d115664 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92398, d115664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92529 q = 1) (hb : d115792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92529, d115792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92529, d115792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92530 q = 1) (hb : d115793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92530, d115793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92530, d115793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92531 q = 1) (hb : d115794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92531, d115794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92531, d115794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92552 q = 1) (hb : d115814 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92552, d115814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92552, d115814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28733 (p : Pattern) (ha : d92558 p = 1) (hb : d115820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92504 q = 1) (hb : d115771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92504, d115771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28717 q ha hb
    | true =>
      simp only [d92504, d115771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28715 q hb ha
  have h2 (q : Pattern) (ha : d92505 q = 1) (hb : d115772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92505, d115772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92505, d115772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92506 q = 1) (hb : d115773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92506, d115773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92506, d115773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92507 q = 1) (hb : d115774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92507, d115774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92507, d115774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92511 q = 1) (hb : d115778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92511, d115778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28718 q ha hb
    | true =>
      simp only [d92511, d115778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28716 q hb ha
  have h6 (q : Pattern) (ha : d92512 q = 1) (hb : d115779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92512, d115779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92512, d115779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92513 q = 1) (hb : d115780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92513, d115780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92513, d115780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92527 q = 1) (hb : d115790 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92527, d115790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28722 q ha hb
    | true =>
      simp only [d92527, d115790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28723 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d92484 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d92528 q = 1) (hb : d115791 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92528, d115791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92528, d115791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d92533 q = 1) (hb : d115796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92533, d115796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28724 q ha hb
    | true =>
      simp only [d92533, d115796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92534 q = 1) (hb : d115797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92534, d115797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92534, d115797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92535 q = 1) (hb : d115798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92535, d115798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92535, d115798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92536 q = 1) (hb : d115799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92536, d115799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92536, d115799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92537 q = 1) (hb : d115800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92537, d115800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92537, d115800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92540 q = 1) (hb : d115803 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92540, d115803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28728 q ha hb
    | true =>
      simp only [d92540, d115803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28726 q hb ha
  have h17 (q : Pattern) (ha : d92541 q = 1) (hb : d115804 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92541, d115804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92541, d115804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d92542 q = 1) (hb : d115805 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92542, d115805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92542, d115805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d92543 q = 1) (hb : d115806 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92543, d115806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92543, d115806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d92545 q = 1) (hb : d115808 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92545, d115808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28729 q ha hb
    | true =>
      simp only [d92545, d115808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28727 q hb ha
  have h21 (q : Pattern) (ha : d92546 q = 1) (hb : d115809 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92546, d115809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92546, d115809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d92547 q = 1) (hb : d115810 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92547, d115810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92547, d115810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92550 q = 1) (hb : d115812 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92550, d115812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28730 q ha hb
    | true =>
      simp only [d92550, d115812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28731 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d92493 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d92551 q = 1) (hb : d115813 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d115813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d92551, d115813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d92553 q = 1) (hb : d115815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92553, d115815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28732 q ha hb
    | true =>
      simp only [d92553, d115815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d92554 q = 1) (hb : d115816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92554, d115816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d92554, d115816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d92555 q = 1) (hb : d115817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d115817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d92555, d115817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d92556 q = 1) (hb : d115818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92556, d115818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d92556, d115818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d92557 q = 1) (hb : d115819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92557, d115819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92557, d115819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d92558 q = 1) (hb : d115820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92558, d115820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d92558, d115820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro28734 (p : Pattern) (ha : d92565 p = 1) (hb : d115822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92560 q = 1) (hb : d115751 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92560, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28723 q ha hb
    | true =>
      simp only [d92560, d115751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q hb ha
  have h2 (q : Pattern) (ha : d92561 q = 1) (hb : d115752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92561, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92561, d115752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92562 q = 1) (hb : d115753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92562, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92562, d115753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92563 q = 1) (hb : d115754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92563, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92563, d115754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92564 q = 1) (hb : d115755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92564, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92564, d115755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12569 q = 1) (hb : d52337 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12569, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28704 q ha hb
    | true =>
      simp only [d12569, d52337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12570 q = 1) (hb : d52338 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12570, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12570, d52338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12571 q = 1) (hb : d52339 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12571, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12571, d52339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12572 q = 1) (hb : d52340 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12572, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12572, d52340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12573 q = 1) (hb : d52341 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12573, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12573, d52341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92565 q = 1) (hb : d115822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92565, d115822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92565, d115822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro28735 (p : Pattern) (ha : d92572 p = 1) (hb : d115829 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92550 q = 1) (hb : d115812 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92550, d115812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28730 q ha hb
    | true =>
      simp only [d92550, d115812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28731 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92493 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92551 q = 1) (hb : d115813 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92551, d115813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92551, d115813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92553 q = 1) (hb : d115815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92553, d115815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28732 q ha hb
    | true =>
      simp only [d92553, d115815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92554 q = 1) (hb : d115816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92554, d115816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92554, d115816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92555 q = 1) (hb : d115817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92555, d115817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92555, d115817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92570 q = 1) (hb : d115827 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92570, d115827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92570, d115827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92571 q = 1) (hb : d115828 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92571, d115828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92571, d115828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92572 q = 1) (hb : d115829 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92572, d115829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92572, d115829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28736 (p : Pattern) (ha : d81633 p = 1) (hb : d115716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12387 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q ha hb
    | true =>
      simp only [d12387, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
  have h2 (q : Pattern) (ha : d12388 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12389 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d81631 q = 1) (hb : d115714 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81631, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d81631, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d6079 q = 1) (hb : d75841 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q ha hb
    | true =>
      simp only [d6079, d75841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
  have h6 (q : Pattern) (ha : d6080 q = 1) (hb : d75842 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6080, d75842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d6081 q = 1) (hb : d75843 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6081, d75843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d6082 q = 1) (hb : d75844 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d6082, d75844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d6082, d75844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d81632 q = 1) (hb : d115715 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d81632, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d81632, d115715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d81633 q = 1) (hb : d115716 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d81633, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d81633, d115716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro28737 (p : Pattern) (ha : d12595 p = 1) (hb : d52368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d52363 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d52363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d52290 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro76 q ha hb
    | true =>
      simp only [d543, d52290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d52364 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d52364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d52291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d52365 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d52365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d52366 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d52366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h8 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d663 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d663, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d663, d52367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12595 q = 1) (hb : d52368 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12595, d52368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12595, d52368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro28738 (p : Pattern) (ha : d92580 p = 1) (hb : d115837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12596 q = 1) (hb : d52369 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12596, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28737 q ha hb
    | true =>
      simp only [d12596, d52369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q ha hb
  have h2 (q : Pattern) (ha : d12597 q = 1) (hb : d52370 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12597, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12597, d52370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12598 q = 1) (hb : d52371 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12598, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12598, d52371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92578 q = 1) (hb : d115835 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d92578, d115835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d92578, d115835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d12387 q = 1) (hb : d52184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12387, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22850 q ha hb
    | true =>
      simp only [d12387, d52184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10566 q ha hb
  have h6 (q : Pattern) (ha : d12388 q = 1) (hb : d52185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12388, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12388, d52185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12389 q = 1) (hb : d52186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12389, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12389, d52186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d81631 q = 1) (hb : d115714 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d81631, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d81631, d115714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92579 q = 1) (hb : d115836 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d92579, d115836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92579, d115836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92580 q = 1) (hb : d115837 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d92580, d115837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d92580, d115837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro28739 (p : Pattern) (ha : d92586 p = 1) (hb : d115843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92581 q = 1) (hb : d115838 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92581, d115838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28738 q ha hb
    | true =>
      simp only [d92581, d115838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92582 q = 1) (hb : d115839 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92582, d115839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92582, d115839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d81634 q = 1) (hb : d115717 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81634, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28736 q ha hb
    | true =>
      simp only [d81634, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d81635 q = 1) (hb : d115718 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81635, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81635, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92583 q = 1) (hb : d115840 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92583, d115840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92583, d115840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92584 q = 1) (hb : d115841 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92584, d115841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92584, d115841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92585 q = 1) (hb : d115842 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92585, d115842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92585, d115842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92586 q = 1) (hb : d115843 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92586, d115843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92586, d115843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28740 (p : Pattern) (ha : d92590 p = 1) (hb : d115847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d81634 q = 1) (hb : d115717 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d81634, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28736 q ha hb
    | true =>
      simp only [d81634, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d81635 q = 1) (hb : d115718 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d81635, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d81635, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12623 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12623, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28708 q ha hb
    | true =>
      simp only [d12623, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12624 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12624, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12624, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92587 q = 1) (hb : d115844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92587, d115844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92587, d115844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d92588 q = 1) (hb : d115845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92588, d115845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92588, d115845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92589 q = 1) (hb : d115846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92589, d115846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92589, d115846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92590 q = 1) (hb : d115847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92590, d115847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d92590, d115847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro28741 (p : Pattern) (ha : d92601 p = 1) (hb : d115853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92450 q = 1) (hb : d115717 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d92450, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28697 q ha hb
    | true =>
      simp only [d92450, d115717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92451 q = 1) (hb : d115718 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d92451, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92451, d115718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92598 q = 1) (hb : d115850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d92598, d115850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92598, d115850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92599 q = 1) (hb : d115851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d92599, d115851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92599, d115851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92600 q = 1) (hb : d115852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d92600, d115852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92600, d115852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92601 q = 1) (hb : d115853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d92601, d115853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92601, d115853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro28742 (p : Pattern) (ha : d92607 p = 1) (hb : d115859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92591 q = 1) (hb : d115848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92591, d115848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28739 q ha hb
    | true =>
      simp only [d92591, d115848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28740 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d92596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d92597 q = 1) (hb : d115849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92597, d115849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92597, d115849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92602 q = 1) (hb : d115854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d92602, d115854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28741 q ha hb
    | true =>
      simp only [d92602, d115854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92603 q = 1) (hb : d115855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d92603, d115855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d92603, d115855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92604 q = 1) (hb : d115856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d92604, d115856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92604, d115856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92605 q = 1) (hb : d115857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d92605, d115857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92605, d115857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d92606 q = 1) (hb : d115858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d92606, d115858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92606, d115858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92607 q = 1) (hb : d115859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d92607, d115859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92607, d115859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro28743 (p : Pattern) (ha : d92613 p = 1) (hb : d115865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92490 q = 1) (hb : d115757 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92490, d115757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92490, d115757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28712 q ha hb
  have h2 (q : Pattern) (ha : d92491 q = 1) (hb : d115758 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92491, d115758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d92491, d115758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92499 q = 1) (hb : d115766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92499, d115766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28712 q ha hb
    | true =>
      simp only [d92499, d115766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28714 q ha hb
  have h4 (q : Pattern) (ha : d92500 q = 1) (hb : d115767 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92500, d115767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d92500, d115767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92501 q = 1) (hb : d115768 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92501, d115768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d92501, d115768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92559 q = 1) (hb : d115821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92559, d115821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28725 q ha hb
    | true =>
      simp only [d92559, d115821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28733 q ha hb
  have h7 (q : Pattern) (ha : d92566 q = 1) (hb : d115823 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92566, d115823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28734 q ha hb
    | true =>
      simp only [d92566, d115823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28706 q hb ha
  have h8 (q : Pattern) (ha : d92567 q = 1) (hb : d115824 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92567, d115824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d92567, d115824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92568 q = 1) (hb : d115825 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92568, d115825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d92568, d115825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d92569 q = 1) (hb : d115826 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92569, d115826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d92569, d115826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92573 q = 1) (hb : d115830 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92573, d115830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92573, d115830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28735 q ha hb
  have h12 (q : Pattern) (ha : d12590 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12590, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12590, d52358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28707 q ha hb
  have h13 (q : Pattern) (ha : d92574 q = 1) (hb : d115831 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92574, d115831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d92574, d115831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d92575 q = 1) (hb : d115832 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92575, d115832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d92575, d115832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92576 q = 1) (hb : d115833 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92576, d115833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d92576, d115833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d92577 q = 1) (hb : d115834 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92577, d115834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d92577, d115834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d92608 q = 1) (hb : d115860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d92608, d115860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92608, d115860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28742 q ha hb
  have h18 (q : Pattern) (ha : d12675 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12675, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12675, d52414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28710 q ha hb
  have h19 (q : Pattern) (ha : d92609 q = 1) (hb : d115861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d92609, d115861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d92609, d115861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d92610 q = 1) (hb : d115862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d92610, d115862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d92610, d115862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d92611 q = 1) (hb : d115863 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d92611, d115863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d92611, d115863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d92612 q = 1) (hb : d115864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d92612, d115864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d92612, d115864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d92613 q = 1) (hb : d115865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d92613, d115865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d92613, d115865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro28744 (p : Pattern) (ha : d92619 p = 1) (hb : d115871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92614 q = 1) (hb : d115866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d92614, d115866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92614, d115866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28743 q ha hb
  have h2 (q : Pattern) (ha : d92615 q = 1) (hb : d115867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d92615, d115867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92615, d115867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92616 q = 1) (hb : d115868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d92616, d115868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92616, d115868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92617 q = 1) (hb : d115869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d92617, d115869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92617, d115869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92618 q = 1) (hb : d115870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d92618, d115870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92618, d115870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92619 q = 1) (hb : d115871 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d92619, d115871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d92619, d115871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28745 (p : Pattern) (ha : d12697 p = 1) (hb : d52450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4914 q = 1) (hb : d52440 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10581 q ha hb
    | true =>
      simp only [d4914, d52440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q ha hb
  have h2 (q : Pattern) (ha : d4915 q = 1) (hb : d52441 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4915, d52441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4916 q = 1) (hb : d52442 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4916, d52442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4917 q = 1) (hb : d52444 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d4917, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4917, d52444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12696 q = 1) (hb : d52449 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12696, d52449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12696, d52449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12697 q = 1) (hb : d52450 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12697, d52450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12697, d52450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28746 (p : Pattern) (ha : d12707 p = 1) (hb : d52460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28745 q ha hb
    | true =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d52458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d52459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12707 q = 1) (hb : d52460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12707, d52460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12707, d52460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro28747 (p : Pattern) (ha : d12717 p = 1) (hb : d52470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12698 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28745 q ha hb
    | true =>
      simp only [d12698, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12699 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12699, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12704 q = 1) (hb : d52457 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12704, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12704, d52457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12705 q = 1) (hb : d52458 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12705, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12705, d52458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12706 q = 1) (hb : d52459 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12706, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12706, d52459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12717 q = 1) (hb : d52470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12717, d52470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12717, d52470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro28748 (p : Pattern) (ha : d12839 p = 1) (hb : d52569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12828 q = 1) (hb : d52558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12828, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28746 q ha hb
    | true =>
      simp only [d12828, d52558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12829 q = 1) (hb : d52559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12829, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12829, d52559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12830 q = 1) (hb : d52560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12830, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12830, d52560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12831 q = 1) (hb : d52561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12831, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12831, d52561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12832 q = 1) (hb : d52562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12832, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12832, d52562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12834 q = 1) (hb : d52564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28747 q ha hb
    | true =>
      simp only [d12834, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12835 q = 1) (hb : d52565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12836 q = 1) (hb : d52566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12836, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12837 q = 1) (hb : d52567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12838 q = 1) (hb : d52568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12839 q = 1) (hb : d52569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12839, d52569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12839, d52569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro28749 (p : Pattern) (ha : d12848 p = 1) (hb : d52578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12834 q = 1) (hb : d52564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12834, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28747 q ha hb
    | true =>
      simp only [d12834, d52564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12835 q = 1) (hb : d52565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12835, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12835, d52565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12836 q = 1) (hb : d52566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12836, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12836, d52566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12837 q = 1) (hb : d52567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12837, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12837, d52567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12838 q = 1) (hb : d52568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12838, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12838, d52568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12848 q = 1) (hb : d52578 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12848, d52578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12848, d52578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
