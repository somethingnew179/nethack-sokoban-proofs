import NetHack.Soko22Hazard87.AndIntroBlocks0050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro12750 (p : Pattern) (ha : d96498 p = 1) (hb : d97705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96489 q = 1) (hb : d97700 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96489, d97700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12749 q ha hb
    | true =>
      simp only [d96489, d97700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96490 q = 1) (hb : d97701 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96490, d97701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96490, d97701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96494 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96495 q = 1) (hb : d97702 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96495, d97702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96495, d97702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96496 q = 1) (hb : d97703 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96496, d97703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96496, d97703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96497 q = 1) (hb : d97704 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96497, d97704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96497, d97704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96498 q = 1) (hb : d97705 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96498, d97705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96498, d97705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12751 (p : Pattern) (ha : d96492 p = 1) (hb : d97707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6079 q = 1) (hb : d96356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d96356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12720 q ha hb
    | true =>
      simp only [d6079, d96356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q ha hb
  have h3 (q : Pattern) (ha : d6080 q = 1) (hb : d96357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d96357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6080, d96357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6081 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d96358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6081, d96358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96358 q = 1) (hb : d97585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96491 q = 1) (hb : d97706 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96491, d97706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96491, d97706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d96492 q = 1) (hb : d97707 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96492, d97707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96492, d97707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12752 (p : Pattern) (ha : d96502 p = 1) (hb : d97713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96493 q = 1) (hb : d97708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96493, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12751 q ha hb
    | true =>
      simp only [d96493, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96494 q = 1) (hb : d97709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96494, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96494, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96260 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96499 q = 1) (hb : d97710 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96499, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96499, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96500 q = 1) (hb : d97711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96500, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96500, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96501 q = 1) (hb : d97712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96501, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96501, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96502 q = 1) (hb : d97713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96502, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96502, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12753 (p : Pattern) (ha : d96360 p = 1) (hb : d97707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6079 q = 1) (hb : d96356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6079, d96356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12720 q ha hb
    | true =>
      simp only [d6079, d96356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12701 q ha hb
  have h3 (q : Pattern) (ha : d6080 q = 1) (hb : d96357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6080, d96357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6080, d96357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6081 q = 1) (hb : d96358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6081, d96358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6081, d96358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96358 q = 1) (hb : d97585 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96256 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96359 q = 1) (hb : d97706 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96359, d97706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96359, d97706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96360 q = 1) (hb : d97707 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96360, d97707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96360, d97707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12754 (p : Pattern) (ha : d96508 p = 1) (hb : d97713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96361 q = 1) (hb : d97708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96361, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12753 q ha hb
    | true =>
      simp only [d96361, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96362 q = 1) (hb : d97709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96362, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96362, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96505 q = 1) (hb : d97710 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96505, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96505, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96506 q = 1) (hb : d97711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96506, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96506, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96507 q = 1) (hb : d97712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96507, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96507, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96508 q = 1) (hb : d97713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96508, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96508, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12755 (p : Pattern) (ha : d96514 p = 1) (hb : d97721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96503 q = 1) (hb : d97714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96503, d97714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12750 q ha hb
    | true =>
      simp only [d96503, d97714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12752 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96367 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96504 q = 1) (hb : d97715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96504, d97715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96504, d97715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96509 q = 1) (hb : d97716 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96509, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12754 q ha hb
    | true =>
      simp only [d96509, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96510 q = 1) (hb : d97717 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96510, d97717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96510, d97717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96511 q = 1) (hb : d97718 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96511, d97718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96511, d97718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96512 q = 1) (hb : d97719 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96512, d97719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96512, d97719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96513 q = 1) (hb : d97720 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96513, d97720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96513, d97720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96514 q = 1) (hb : d97721 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96514, d97721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96514, d97721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12756 (p : Pattern) (ha : d96526 p = 1) (hb : d97727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96390 q = 1) (hb : d97626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96390, d97626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96390, d97626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12728 q ha hb
  have h2 (q : Pattern) (ha : d96391 q = 1) (hb : d97627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96391, d97627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96391, d97627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96397 q = 1) (hb : d97635 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96397, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12728 q ha hb
    | true =>
      simp only [d96397, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12730 q ha hb
  have h4 (q : Pattern) (ha : d96398 q = 1) (hb : d97636 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96398, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96398, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96399 q = 1) (hb : d97637 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96399, d97637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96399, d97637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96463 q = 1) (hb : d97683 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96463, d97683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12739 q ha hb
    | true =>
      simp only [d96463, d97683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12745 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96293 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96470 q = 1) (hb : d97685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96470, d97685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12746 q ha hb
    | true =>
      simp only [d96470, d97685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96471 q = 1) (hb : d97686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96471, d97686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96471, d97686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96472 q = 1) (hb : d97687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96472, d97687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96472, d97687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d96473 q = 1) (hb : d97688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96473, d97688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96473, d97688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96477 q = 1) (hb : d97692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96477, d97692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96477, d97692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12747 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d96479 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d96480 q = 1) (hb : d97693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96480, d97693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96480, d97693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d96481 q = 1) (hb : d97694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96481, d97694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d96481, d97694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d96482 q = 1) (hb : d97695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96482, d97695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96482, d97695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d96483 q = 1) (hb : d97696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96483, d97696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96483, d97696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96515 q = 1) (hb : d97722 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96515, d97722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96515, d97722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12755 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d96521 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d96522 q = 1) (hb : d97723 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96522, d97723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d96522, d97723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d96523 q = 1) (hb : d97724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96523, d97724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d96523, d97724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d96524 q = 1) (hb : d97725 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96524, d97725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d96524, d97725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d96525 q = 1) (hb : d97726 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96525, d97726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d96525, d97726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d96526 q = 1) (hb : d97727 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96526, d97727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96526, d97727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro12757 (p : Pattern) (ha : d96532 p = 1) (hb : d97733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96527 q = 1) (hb : d97728 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96527, d97728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96527, d97728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12756 q ha hb
  have h2 (q : Pattern) (ha : d96528 q = 1) (hb : d97729 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96528, d97729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96528, d97729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96529 q = 1) (hb : d97730 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96529, d97730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96529, d97730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96530 q = 1) (hb : d97731 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96530, d97731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96530, d97731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96531 q = 1) (hb : d97732 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96531, d97732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96531, d97732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96532 q = 1) (hb : d97733 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96532, d97733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96532, d97733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12758 (p : Pattern) (ha : d762 p = 1) (hb : d52434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d762 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12759 (p : Pattern) (ha : d4913 p = 1) (hb : d52432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d52432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d4913 q = 1) (hb : d52432 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12760 (p : Pattern) (ha : d96541 p = 1) (hb : d97737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96536 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4914 q = 1) (hb : d96534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d96534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12759 q ha hb
    | true =>
      simp only [d4914, d96534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12758 q ha hb
  have h3 (q : Pattern) (ha : d4915 q = 1) (hb : d96535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d96535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4915, d96535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4916 q = 1) (hb : d96536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d96536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4916, d96536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96536 q = 1) (hb : d97735 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96539 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96540 q = 1) (hb : d97736 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96540, d97736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96540, d97736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96541 q = 1) (hb : d97737 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96541, d97737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96541, d97737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12761 (p : Pattern) (ha : d96551 p = 1) (hb : d97743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96542 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12760 q ha hb
    | true =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96543 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96548 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96549 q = 1) (hb : d97741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96549, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96549, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96550 q = 1) (hb : d97742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96550, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96550, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96551 q = 1) (hb : d97743 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96551, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96551, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12762 (p : Pattern) (ha : d96561 p = 1) (hb : d97749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96556 q = 1) (hb : d97744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96556, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12761 q ha hb
    | true =>
      simp only [d96556, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96557 q = 1) (hb : d97745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96557, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96557, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96558 q = 1) (hb : d97746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96558, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96558, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96559 q = 1) (hb : d97747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96559, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96559, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96560 q = 1) (hb : d97748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96560, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96560, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96561 q = 1) (hb : d97749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96561, d97749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96561, d97749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12763 (p : Pattern) (ha : d96564 p = 1) (hb : d97752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96542 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12760 q ha hb
    | true =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96543 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96548 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96549 q = 1) (hb : d97741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96549, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96549, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96550 q = 1) (hb : d97742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96550, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96550, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96564 q = 1) (hb : d97752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96564, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96564, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12764 (p : Pattern) (ha : d96571 p = 1) (hb : d97758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96556 q = 1) (hb : d97744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96556, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12761 q ha hb
    | true =>
      simp only [d96556, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96557 q = 1) (hb : d97745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96557, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96557, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96558 q = 1) (hb : d97746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96558, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96558, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96559 q = 1) (hb : d97747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96559, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96559, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96560 q = 1) (hb : d97748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96560, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96560, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96565 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96566 q = 1) (hb : d97753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96566, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12763 q ha hb
    | true =>
      simp only [d96566, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96567 q = 1) (hb : d97754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96567, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96567, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96568 q = 1) (hb : d97755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96568, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96568, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d96569 q = 1) (hb : d97756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96569, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96569, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96570 q = 1) (hb : d97757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96570, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96570, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d96571 q = 1) (hb : d97758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96571, d97758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96571, d97758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12765 (p : Pattern) (ha : d96576 p = 1) (hb : d97763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96542 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12760 q ha hb
    | true =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96543 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96548 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96549 q = 1) (hb : d97741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96549, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96549, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96575 q = 1) (hb : d97762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96575, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96575, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96576 q = 1) (hb : d97763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96576, d97763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96576, d97763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12766 (p : Pattern) (ha : d96585 p = 1) (hb : d97770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96542 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12760 q ha hb
    | true =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96543 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96548 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96583 q = 1) (hb : d97768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96583, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96583, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96584 q = 1) (hb : d97769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96584, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96584, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96585 q = 1) (hb : d97770 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96585, d97770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96585, d97770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12767 (p : Pattern) (ha : d12489 p = 1) (hb : d52294 p = 1) : d0 p = 1 := by
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
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12489 q = 1) (hb : d52294 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12768 (p : Pattern) (ha : d96596 p = 1) (hb : d97776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12688 q = 1) (hb : d96592 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12688, d96592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12767 q ha hb
    | true =>
      simp only [d12688, d96592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12759 q ha hb
  have h3 (q : Pattern) (ha : d12689 q = 1) (hb : d96593 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12689, d96593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12689, d96593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12690 q = 1) (hb : d96594 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12690, d96594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12690, d96594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96594 q = 1) (hb : d97774 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96536 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4914 q = 1) (hb : d96534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d96534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12759 q ha hb
    | true =>
      simp only [d4914, d96534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12758 q ha hb
  have h8 (q : Pattern) (ha : d4915 q = 1) (hb : d96535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d96535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4915, d96535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4916 q = 1) (hb : d96536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d96536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4916, d96536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96536 q = 1) (hb : d97735 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96595 q = 1) (hb : d97775 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96595, d97775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96595, d97775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96596 q = 1) (hb : d97776 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96596, d97776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96596, d97776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12769 (p : Pattern) (ha : d96606 p = 1) (hb : d97782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96597 q = 1) (hb : d97777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96597, d97777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12768 q ha hb
    | true =>
      simp only [d96597, d97777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96598 q = 1) (hb : d97778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96598, d97778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96598, d97778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96602 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96603 q = 1) (hb : d97779 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96603, d97779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96603, d97779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96604 q = 1) (hb : d97780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96604, d97780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96604, d97780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96605 q = 1) (hb : d97781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96605, d97781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96605, d97781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96606 q = 1) (hb : d97782 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96606, d97782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96606, d97782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12770 (p : Pattern) (ha : d96600 p = 1) (hb : d97737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96536 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d4914 q = 1) (hb : d96534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d4914, d96534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12759 q ha hb
    | true =>
      simp only [d4914, d96534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12758 q ha hb
  have h3 (q : Pattern) (ha : d4915 q = 1) (hb : d96535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d4915, d96535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4915, d96535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d4916 q = 1) (hb : d96536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d4916, d96536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4916, d96536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96536 q = 1) (hb : d97735 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96599 q = 1) (hb : d97736 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96599, d97736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96599, d97736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d96600 q = 1) (hb : d97737 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96600, d97737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96600, d97737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12771 (p : Pattern) (ha : d96610 p = 1) (hb : d97743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12770 q ha hb
    | true =>
      simp only [d96601, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96607 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96607, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96607, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96608 q = 1) (hb : d97741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96608, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96608, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96609 q = 1) (hb : d97742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96609, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96609, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96610 q = 1) (hb : d97743 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96610, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96610, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12772 (p : Pattern) (ha : d96616 p = 1) (hb : d97743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96542 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12760 q ha hb
    | true =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96543 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96613 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96613, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96613, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96614 q = 1) (hb : d97741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96614, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96614, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96615 q = 1) (hb : d97742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96615, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96615, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96616 q = 1) (hb : d97743 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96616, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96616, d97743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12773 (p : Pattern) (ha : d96622 p = 1) (hb : d97789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96579 q = 1) (hb : d97764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96579, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12765 q ha hb
    | true =>
      simp only [d96579, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96580 q = 1) (hb : d97765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96580, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96580, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96581 q = 1) (hb : d97766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96581, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96581, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96582 q = 1) (hb : d97767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96582, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96582, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96588 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96589 q = 1) (hb : d97771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96589, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12766 q ha hb
    | true =>
      simp only [d96589, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96590 q = 1) (hb : d97772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96590, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96590, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96591 q = 1) (hb : d97773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96591, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96591, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d96611 q = 1) (hb : d97783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96611, d97783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12769 q ha hb
    | true =>
      simp only [d96611, d97783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12771 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96556 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d96612 q = 1) (hb : d97784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96612, d97784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96612, d97784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d96617 q = 1) (hb : d97744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96617, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12772 q ha hb
    | true =>
      simp only [d96617, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96618 q = 1) (hb : d97785 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96618, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96618, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96619 q = 1) (hb : d97786 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96619, d97786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96619, d97786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96620 q = 1) (hb : d97787 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96620, d97787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96620, d97787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d96621 q = 1) (hb : d97788 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96621, d97788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96621, d97788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96622 q = 1) (hb : d97789 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96622, d97789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96622, d97789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro12774 (p : Pattern) (ha : d96623 p = 1) (hb : d97790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96542 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12760 q ha hb
    | true =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96543 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96548 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96549 q = 1) (hb : d97741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96549, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96549, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96575 q = 1) (hb : d97762 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96575, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96575, d97762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96623 q = 1) (hb : d97790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96623, d97790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96623, d97790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12775 (p : Pattern) (ha : d96629 p = 1) (hb : d97795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96542 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12760 q ha hb
    | true =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96543 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96548 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96548, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96583 q = 1) (hb : d97768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96583, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96583, d97768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96584 q = 1) (hb : d97769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96584, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96584, d97769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96629 q = 1) (hb : d97795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96629, d97795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96629, d97795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12776 (p : Pattern) (ha : d96634 p = 1) (hb : d97799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96597 q = 1) (hb : d97777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96597, d97777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12768 q ha hb
    | true =>
      simp only [d96597, d97777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96598 q = 1) (hb : d97778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96598, d97778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96598, d97778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96602 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96603 q = 1) (hb : d97779 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96603, d97779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96603, d97779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96604 q = 1) (hb : d97780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96604, d97780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96604, d97780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96605 q = 1) (hb : d97781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96605, d97781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96605, d97781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96634 q = 1) (hb : d97799 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96634, d97799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96634, d97799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12777 (p : Pattern) (ha : d96635 p = 1) (hb : d97752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96601 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96601, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12770 q ha hb
    | true =>
      simp only [d96601, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96602 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96602, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96602, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96547 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96607 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96607, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96607, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96608 q = 1) (hb : d97741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96608, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96608, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96609 q = 1) (hb : d97742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96609, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96609, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96635 q = 1) (hb : d97752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96635, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96635, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12778 (p : Pattern) (ha : d96638 p = 1) (hb : d97752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96542 q = 1) (hb : d97738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12760 q ha hb
    | true =>
      simp only [d96542, d97738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96543 q = 1) (hb : d97739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96543, d97739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96613 q = 1) (hb : d97740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96613, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96613, d97740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96614 q = 1) (hb : d97741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96614, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96614, d97741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96615 q = 1) (hb : d97742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96615, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96615, d97742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96638 q = 1) (hb : d97752 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96638, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96638, d97752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12779 (p : Pattern) (ha : d96644 p = 1) (hb : d97806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96578 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96579 q = 1) (hb : d97764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96579, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12765 q ha hb
    | true =>
      simp only [d96579, d97764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96580 q = 1) (hb : d97765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96580, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96580, d97765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96581 q = 1) (hb : d97766 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96581, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96581, d97766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96582 q = 1) (hb : d97767 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96582, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96582, d97767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96588 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96589 q = 1) (hb : d97771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96589, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12766 q ha hb
    | true =>
      simp only [d96589, d97771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96590 q = 1) (hb : d97772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96590, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96590, d97772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96591 q = 1) (hb : d97773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96591, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96591, d97773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d96611 q = 1) (hb : d97783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96611, d97783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12769 q ha hb
    | true =>
      simp only [d96611, d97783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12771 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96556 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d96612 q = 1) (hb : d97784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96612, d97784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96612, d97784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d96617 q = 1) (hb : d97744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96617, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12772 q ha hb
    | true =>
      simp only [d96617, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96618 q = 1) (hb : d97785 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96618, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96618, d97785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96619 q = 1) (hb : d97786 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96619, d97786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96619, d97786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96620 q = 1) (hb : d97787 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96620, d97787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96620, d97787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d96621 q = 1) (hb : d97788 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96621, d97788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96621, d97788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d96624 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d96625 q = 1) (hb : d97791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96625, d97791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12774 q ha hb
    | true =>
      simp only [d96625, d97791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d96626 q = 1) (hb : d97792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96626, d97792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96626, d97792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d96627 q = 1) (hb : d97793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96627, d97793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d96627, d97793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d96628 q = 1) (hb : d97794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96628, d97794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96628, d97794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d96630 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d96631 q = 1) (hb : d97796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96631, d97796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12775 q ha hb
    | true =>
      simp only [d96631, d97796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d96632 q = 1) (hb : d97797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96632, d97797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96632, d97797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d96633 q = 1) (hb : d97798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96633, d97798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d96633, d97798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d96636 q = 1) (hb : d97800 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96636, d97800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12776 q ha hb
    | true =>
      simp only [d96636, d97800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12777 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d96566 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d96637 q = 1) (hb : d97801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96637, d97801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d96637, d97801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d96639 q = 1) (hb : d97753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96639, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12778 q ha hb
    | true =>
      simp only [d96639, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d96640 q = 1) (hb : d97802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96640, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d96640, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d96641 q = 1) (hb : d97803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96641, d97803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d96641, d97803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d96642 q = 1) (hb : d97804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96642, d97804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d96642, d97804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d96643 q = 1) (hb : d97805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96643, d97805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d96643, d97805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d96644 q = 1) (hb : d97806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96644, d97806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96644, d97806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro12780 (p : Pattern) (ha : d96656 p = 1) (hb : d97808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96646 q = 1) (hb : d97744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96646, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12771 q ha hb
    | true =>
      simp only [d96646, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96647 q = 1) (hb : d97745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96647, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96647, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96648 q = 1) (hb : d97746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96648, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96648, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96649 q = 1) (hb : d97747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96649, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96649, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96650 q = 1) (hb : d97748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96650, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96650, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96655 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96656 q = 1) (hb : d97808 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96656, d97808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96656, d97808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro12781 (p : Pattern) (ha : d96669 p = 1) (hb : d97815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96636 q = 1) (hb : d97800 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96636, d97800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12776 q ha hb
    | true =>
      simp only [d96636, d97800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12777 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96566 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96637 q = 1) (hb : d97801 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96637, d97801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96637, d97801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96639 q = 1) (hb : d97753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96639, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12778 q ha hb
    | true =>
      simp only [d96639, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96640 q = 1) (hb : d97802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96640, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96640, d97802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96641 q = 1) (hb : d97803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96641, d97803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96641, d97803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96667 q = 1) (hb : d97813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96667, d97813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96667, d97813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96668 q = 1) (hb : d97814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96668, d97814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96668, d97814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96669 q = 1) (hb : d97815 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96669, d97815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96669, d97815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12782 (p : Pattern) (ha : d986 p = 1) (hb : d52599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d986 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12783 (p : Pattern) (ha : d6210 p = 1) (hb : d52594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42 q ha hb
    | true =>
      simp only [d319, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d52594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6210 q = 1) (hb : d52594 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12784 (p : Pattern) (ha : d12595 p = 1) (hb : d52367 p = 1) : d0 p = 1 := by
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
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12595 q = 1) (hb : d52367 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12785 (p : Pattern) (ha : d96684 p = 1) (hb : d97824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96679 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12868 q = 1) (hb : d96677 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12868, d96677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12784 q ha hb
    | true =>
      simp only [d12868, d96677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12783 q ha hb
  have h3 (q : Pattern) (ha : d12869 q = 1) (hb : d96678 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12869, d96678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12869, d96678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12870 q = 1) (hb : d96679 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12870, d96679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12870, d96679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96679 q = 1) (hb : d97821 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96682 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d6211 q = 1) (hb : d96680 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d96680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12783 q ha hb
    | true =>
      simp only [d6211, d96680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12782 q ha hb
  have h8 (q : Pattern) (ha : d6212 q = 1) (hb : d96681 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d96681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6212, d96681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d6213 q = 1) (hb : d96682 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d96682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6213, d96682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96682 q = 1) (hb : d97822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96683 q = 1) (hb : d97823 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96683, d97823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96683, d97823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96684 q = 1) (hb : d97824 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96684, d97824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96684, d97824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12786 (p : Pattern) (ha : d96694 p = 1) (hb : d97830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96685 q = 1) (hb : d97825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96685, d97825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12785 q ha hb
    | true =>
      simp only [d96685, d97825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96686 q = 1) (hb : d97826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96686, d97826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96686, d97826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96690 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96691 q = 1) (hb : d97827 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96691, d97827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96691, d97827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96692 q = 1) (hb : d97828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96692, d97828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96692, d97828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96693 q = 1) (hb : d97829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96693, d97829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96693, d97829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96694 q = 1) (hb : d97830 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96694, d97830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96694, d97830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12787 (p : Pattern) (ha : d96688 p = 1) (hb : d97832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6211 q = 1) (hb : d96680 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d96680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12783 q ha hb
    | true =>
      simp only [d6211, d96680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12782 q ha hb
  have h3 (q : Pattern) (ha : d6212 q = 1) (hb : d96681 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d96681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6212, d96681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6213 q = 1) (hb : d96682 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d96682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6213, d96682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96682 q = 1) (hb : d97822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96687 q = 1) (hb : d97831 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96687, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96687, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d96688 q = 1) (hb : d97832 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96688, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96688, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12788 (p : Pattern) (ha : d96705 p = 1) (hb : d97838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96689 q = 1) (hb : d97833 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96689, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12787 q ha hb
    | true =>
      simp only [d96689, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96690 q = 1) (hb : d97834 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96690, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96690, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96701 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96702 q = 1) (hb : d97835 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96702, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96702, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96703 q = 1) (hb : d97836 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96703, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96703, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96704 q = 1) (hb : d97837 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96704, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96704, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96705 q = 1) (hb : d97838 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96705, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96705, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12789 (p : Pattern) (ha : d96708 p = 1) (hb : d97832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6211 q = 1) (hb : d96680 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d6211, d96680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12783 q ha hb
    | true =>
      simp only [d6211, d96680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12782 q ha hb
  have h3 (q : Pattern) (ha : d6212 q = 1) (hb : d96681 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d6212, d96681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6212, d96681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d6213 q = 1) (hb : d96682 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d6213, d96682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d6213, d96682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96682 q = 1) (hb : d97822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96697 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96707 q = 1) (hb : d97831 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96707, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96707, d97831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96708 q = 1) (hb : d97832 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96708, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96708, d97832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12790 (p : Pattern) (ha : d96724 p = 1) (hb : d97838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96709 q = 1) (hb : d97833 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96709, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12789 q ha hb
    | true =>
      simp only [d96709, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96710 q = 1) (hb : d97834 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96710, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96710, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96721 q = 1) (hb : d97835 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96721, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96721, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96722 q = 1) (hb : d97836 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96722, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96722, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96723 q = 1) (hb : d97837 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96723, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96723, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96724 q = 1) (hb : d97838 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96724, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96724, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12791 (p : Pattern) (ha : d96730 p = 1) (hb : d97846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96706 q = 1) (hb : d97839 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96706, d97839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12786 q ha hb
    | true =>
      simp only [d96706, d97839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12788 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96719 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96720 q = 1) (hb : d97840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96720, d97840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96720, d97840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96725 q = 1) (hb : d97841 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96725, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12790 q ha hb
    | true =>
      simp only [d96725, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96726 q = 1) (hb : d97842 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96726, d97842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96726, d97842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96727 q = 1) (hb : d97843 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96727, d97843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96727, d97843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96728 q = 1) (hb : d97844 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96728, d97844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96728, d97844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96729 q = 1) (hb : d97845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96729, d97845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96729, d97845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96730 q = 1) (hb : d97846 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96730, d97846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96730, d97846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12792 (p : Pattern) (ha : d96743 p = 1) (hb : d97852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96562 q = 1) (hb : d97750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96562, d97750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96562, d97750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12762 q ha hb
  have h2 (q : Pattern) (ha : d96563 q = 1) (hb : d97751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96563, d97751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96563, d97751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96572 q = 1) (hb : d97759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96572, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12762 q ha hb
    | true =>
      simp only [d96572, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12764 q ha hb
  have h4 (q : Pattern) (ha : d96573 q = 1) (hb : d97760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96573, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96573, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96574 q = 1) (hb : d97761 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96574, d97761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96574, d97761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96645 q = 1) (hb : d97807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96645, d97807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12773 q ha hb
    | true =>
      simp only [d96645, d97807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12779 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96662 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96663 q = 1) (hb : d97809 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96663, d97809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12780 q ha hb
    | true =>
      simp only [d96663, d97809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96664 q = 1) (hb : d97810 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96664, d97810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96664, d97810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96665 q = 1) (hb : d97811 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96665, d97811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96665, d97811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d96666 q = 1) (hb : d97812 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96666, d97812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96666, d97812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96670 q = 1) (hb : d97816 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96670, d97816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96670, d97816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12781 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d96672 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d96673 q = 1) (hb : d97817 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96673, d97817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96673, d97817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d96674 q = 1) (hb : d97818 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96674, d97818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d96674, d97818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d96675 q = 1) (hb : d97819 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96675, d97819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96675, d97819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d96676 q = 1) (hb : d97820 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96676, d97820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96676, d97820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96731 q = 1) (hb : d97847 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96731, d97847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96731, d97847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12791 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d96738 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d96739 q = 1) (hb : d97848 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96739, d97848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d96739, d97848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d96740 q = 1) (hb : d97849 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96740, d97849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d96740, d97849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d96741 q = 1) (hb : d97850 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96741, d97850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d96741, d97850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d96742 q = 1) (hb : d97851 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96742, d97851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d96742, d97851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d96743 q = 1) (hb : d97852 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96743, d97852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96743, d97852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro12793 (p : Pattern) (ha : d96749 p = 1) (hb : d97858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96744 q = 1) (hb : d97853 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96744, d97853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96744, d97853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12792 q ha hb
  have h2 (q : Pattern) (ha : d96745 q = 1) (hb : d97854 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96745, d97854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96745, d97854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96746 q = 1) (hb : d97855 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96746, d97855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96746, d97855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96747 q = 1) (hb : d97856 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96747, d97856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96747, d97856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96748 q = 1) (hb : d97857 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96748, d97857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96748, d97857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96749 q = 1) (hb : d97858 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96749, d97858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96749, d97858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12794 (p : Pattern) (ha : d5009 p = 1) (hb : d52706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d52706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5009 q = 1) (hb : d52706 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12795 (p : Pattern) (ha : d12961 p = 1) (hb : d52708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d52704 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d52704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d52705 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d52705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d52708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12961 q = 1) (hb : d52708 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12796 (p : Pattern) (ha : d96759 p = 1) (hb : d97863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12962 q = 1) (hb : d96752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d96752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12794 q ha hb
    | true =>
      simp only [d12962, d96752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12795 q ha hb
  have h3 (q : Pattern) (ha : d12963 q = 1) (hb : d96753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d96753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12963, d96753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12964 q = 1) (hb : d96754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d96754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12964, d96754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96754 q = 1) (hb : d97861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96757 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96758 q = 1) (hb : d97862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96758, d97862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96758, d97862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96759 q = 1) (hb : d97863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96759, d97863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96759, d97863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12797 (p : Pattern) (ha : d96769 p = 1) (hb : d97869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96760 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12796 q ha hb
    | true =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96761 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96766 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96767 q = 1) (hb : d97867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96767, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96767, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96768 q = 1) (hb : d97868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96768, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96768, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96769 q = 1) (hb : d97869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96769, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96769, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12798 (p : Pattern) (ha : d96779 p = 1) (hb : d97875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96774 q = 1) (hb : d97870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96774, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12797 q ha hb
    | true =>
      simp only [d96774, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96775 q = 1) (hb : d97871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96775, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96775, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96776 q = 1) (hb : d97872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96776, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96776, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96777 q = 1) (hb : d97873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96777, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96777, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96778 q = 1) (hb : d97874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96778, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96778, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96779 q = 1) (hb : d97875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96779, d97875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96779, d97875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12799 (p : Pattern) (ha : d96782 p = 1) (hb : d97878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96760 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12796 q ha hb
    | true =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96761 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96766 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96767 q = 1) (hb : d97867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96767, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96767, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96768 q = 1) (hb : d97868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96768, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96768, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96782 q = 1) (hb : d97878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96782, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96782, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12800 (p : Pattern) (ha : d96789 p = 1) (hb : d97884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96774 q = 1) (hb : d97870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96774, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12797 q ha hb
    | true =>
      simp only [d96774, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96775 q = 1) (hb : d97871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96775, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96775, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96776 q = 1) (hb : d97872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96776, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96776, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96777 q = 1) (hb : d97873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96777, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96777, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96778 q = 1) (hb : d97874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96778, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96778, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96783 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96784 q = 1) (hb : d97879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96784, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12799 q ha hb
    | true =>
      simp only [d96784, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96785 q = 1) (hb : d97880 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96785, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96785, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96786 q = 1) (hb : d97881 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96786, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96786, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d96787 q = 1) (hb : d97882 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96787, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96787, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96788 q = 1) (hb : d97883 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96788, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96788, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d96789 q = 1) (hb : d97884 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96789, d97884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96789, d97884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12801 (p : Pattern) (ha : d96794 p = 1) (hb : d97889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96760 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12796 q ha hb
    | true =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96761 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96766 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96767 q = 1) (hb : d97867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96767, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96767, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96793 q = 1) (hb : d97888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96793, d97888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96793, d97888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96794 q = 1) (hb : d97889 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96794, d97889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96794, d97889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12802 (p : Pattern) (ha : d96803 p = 1) (hb : d97896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96760 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12796 q ha hb
    | true =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96761 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96766 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96801 q = 1) (hb : d97894 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96801, d97894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96801, d97894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96802 q = 1) (hb : d97895 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96802, d97895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96802, d97895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96803 q = 1) (hb : d97896 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96803, d97896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96803, d97896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12803 (p : Pattern) (ha : d12956 p = 1) (hb : d52695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d52683 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d52683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d52684 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d52684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1112 q = 1) (hb : d52693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d52693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1113 q = 1) (hb : d52694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1113, d52694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1114 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1114, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1114, d52695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d12956 q = 1) (hb : d52695 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d12956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d12956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12804 (p : Pattern) (ha : d96814 p = 1) (hb : d97902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96812 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12957 q = 1) (hb : d96810 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12957, d96810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12803 q ha hb
    | true =>
      simp only [d12957, d96810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12794 q ha hb
  have h3 (q : Pattern) (ha : d12958 q = 1) (hb : d96811 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12958, d96811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12958, d96811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12959 q = 1) (hb : d96812 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12959, d96812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12959, d96812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96812 q = 1) (hb : d97900 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96754 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d12962 q = 1) (hb : d96752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d96752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12794 q ha hb
    | true =>
      simp only [d12962, d96752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12795 q ha hb
  have h8 (q : Pattern) (ha : d12963 q = 1) (hb : d96753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d96753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12963, d96753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12964 q = 1) (hb : d96754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d96754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12964, d96754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96754 q = 1) (hb : d97861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96813 q = 1) (hb : d97901 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96813, d97901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96813, d97901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96814 q = 1) (hb : d97902 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96814, d97902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96814, d97902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12805 (p : Pattern) (ha : d96824 p = 1) (hb : d97908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96815 q = 1) (hb : d97903 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96815, d97903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12804 q ha hb
    | true =>
      simp only [d96815, d97903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96816 q = 1) (hb : d97904 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96816, d97904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96816, d97904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96820 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96821 q = 1) (hb : d97905 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96821, d97905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96821, d97905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96822 q = 1) (hb : d97906 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96822, d97906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96822, d97906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96823 q = 1) (hb : d97907 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96823, d97907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96823, d97907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96824 q = 1) (hb : d97908 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96824, d97908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96824, d97908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12806 (p : Pattern) (ha : d96818 p = 1) (hb : d97863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96754 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12962 q = 1) (hb : d96752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12962, d96752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12794 q ha hb
    | true =>
      simp only [d12962, d96752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12795 q ha hb
  have h3 (q : Pattern) (ha : d12963 q = 1) (hb : d96753 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12963, d96753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12963, d96753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12964 q = 1) (hb : d96754 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12964, d96754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12964, d96754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96754 q = 1) (hb : d97861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96817 q = 1) (hb : d97862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96817, d97862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96817, d97862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d96818 q = 1) (hb : d97863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96818, d97863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96818, d97863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12807 (p : Pattern) (ha : d96828 p = 1) (hb : d97869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96819 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96819, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12806 q ha hb
    | true =>
      simp only [d96819, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96820 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96820, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96820, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96825 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96825, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96825, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96826 q = 1) (hb : d97867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96826, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96826, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96827 q = 1) (hb : d97868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96827, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96827, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96828 q = 1) (hb : d97869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96828, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96828, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12808 (p : Pattern) (ha : d96834 p = 1) (hb : d97869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96760 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12796 q ha hb
    | true =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96761 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96831 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96831, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96831, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96832 q = 1) (hb : d97867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96832, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96832, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96833 q = 1) (hb : d97868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96833, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96833, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96834 q = 1) (hb : d97869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96834, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96834, d97869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12809 (p : Pattern) (ha : d96840 p = 1) (hb : d97915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96796 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96797 q = 1) (hb : d97890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96797, d97890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12801 q ha hb
    | true =>
      simp only [d96797, d97890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96798 q = 1) (hb : d97891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96798, d97891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96798, d97891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96799 q = 1) (hb : d97892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96799, d97892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96799, d97892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96800 q = 1) (hb : d97893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96800, d97893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96800, d97893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96806 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96807 q = 1) (hb : d97897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96807, d97897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12802 q ha hb
    | true =>
      simp only [d96807, d97897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96808 q = 1) (hb : d97898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96808, d97898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96808, d97898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96809 q = 1) (hb : d97899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96809, d97899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96809, d97899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d96829 q = 1) (hb : d97909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96829, d97909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12805 q ha hb
    | true =>
      simp only [d96829, d97909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12807 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96774 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d96830 q = 1) (hb : d97910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96830, d97910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96830, d97910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d96835 q = 1) (hb : d97870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96835, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12808 q ha hb
    | true =>
      simp only [d96835, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96836 q = 1) (hb : d97911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96836, d97911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96836, d97911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96837 q = 1) (hb : d97912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96837, d97912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96837, d97912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96838 q = 1) (hb : d97913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96838, d97913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96838, d97913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d96839 q = 1) (hb : d97914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96839, d97914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96839, d97914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96840 q = 1) (hb : d97915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96840, d97915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96840, d97915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro12810 (p : Pattern) (ha : d96841 p = 1) (hb : d97916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96760 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12796 q ha hb
    | true =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96761 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96766 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96767 q = 1) (hb : d97867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96767, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96767, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96793 q = 1) (hb : d97888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96793, d97888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96793, d97888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96841 q = 1) (hb : d97916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96841, d97916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96841, d97916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12811 (p : Pattern) (ha : d96847 p = 1) (hb : d97921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96760 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12796 q ha hb
    | true =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96761 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96766 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96766, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96801 q = 1) (hb : d97894 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96801, d97894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96801, d97894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96802 q = 1) (hb : d97895 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96802, d97895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96802, d97895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96847 q = 1) (hb : d97921 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96847, d97921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96847, d97921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12812 (p : Pattern) (ha : d96852 p = 1) (hb : d97925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96815 q = 1) (hb : d97903 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96815, d97903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12804 q ha hb
    | true =>
      simp only [d96815, d97903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96816 q = 1) (hb : d97904 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96816, d97904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96816, d97904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96820 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96821 q = 1) (hb : d97905 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96821, d97905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96821, d97905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96822 q = 1) (hb : d97906 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96822, d97906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96822, d97906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96823 q = 1) (hb : d97907 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96823, d97907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96823, d97907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96852 q = 1) (hb : d97925 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96852, d97925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96852, d97925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12813 (p : Pattern) (ha : d96853 p = 1) (hb : d97878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96819 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96819, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12806 q ha hb
    | true =>
      simp only [d96819, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96820 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96820, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96820, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96825 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96825, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96825, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96826 q = 1) (hb : d97867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96826, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96826, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96827 q = 1) (hb : d97868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96827, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96827, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96853 q = 1) (hb : d97878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96853, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96853, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12814 (p : Pattern) (ha : d96856 p = 1) (hb : d97878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96760 q = 1) (hb : d97864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12796 q ha hb
    | true =>
      simp only [d96760, d97864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96761 q = 1) (hb : d97865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96761, d97865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96831 q = 1) (hb : d97866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96831, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96831, d97866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96832 q = 1) (hb : d97867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96832, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96832, d97867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96833 q = 1) (hb : d97868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96833, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96833, d97868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96856 q = 1) (hb : d97878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96856, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96856, d97878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12815 (p : Pattern) (ha : d96862 p = 1) (hb : d97932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96796 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96797 q = 1) (hb : d97890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96797, d97890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12801 q ha hb
    | true =>
      simp only [d96797, d97890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96798 q = 1) (hb : d97891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96798, d97891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96798, d97891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96799 q = 1) (hb : d97892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96799, d97892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96799, d97892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96800 q = 1) (hb : d97893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96800, d97893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96800, d97893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96806 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96807 q = 1) (hb : d97897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96807, d97897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12802 q ha hb
    | true =>
      simp only [d96807, d97897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96808 q = 1) (hb : d97898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96808, d97898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96808, d97898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96809 q = 1) (hb : d97899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96809, d97899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96809, d97899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d96829 q = 1) (hb : d97909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96829, d97909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12805 q ha hb
    | true =>
      simp only [d96829, d97909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12807 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96774 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d96830 q = 1) (hb : d97910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96830, d97910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96830, d97910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d96835 q = 1) (hb : d97870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96835, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12808 q ha hb
    | true =>
      simp only [d96835, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d96836 q = 1) (hb : d97911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96836, d97911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96836, d97911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d96837 q = 1) (hb : d97912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96837, d97912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96837, d97912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d96838 q = 1) (hb : d97913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96838, d97913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96838, d97913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d96839 q = 1) (hb : d97914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96839, d97914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96839, d97914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d96842 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d96843 q = 1) (hb : d97917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96843, d97917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12810 q ha hb
    | true =>
      simp only [d96843, d97917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d96844 q = 1) (hb : d97918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96844, d97918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96844, d97918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d96845 q = 1) (hb : d97919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96845, d97919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d96845, d97919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d96846 q = 1) (hb : d97920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96846, d97920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96846, d97920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d96848 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d96849 q = 1) (hb : d97922 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96849, d97922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12811 q ha hb
    | true =>
      simp only [d96849, d97922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d96850 q = 1) (hb : d97923 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96850, d97923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96850, d97923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d96851 q = 1) (hb : d97924 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96851, d97924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d96851, d97924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d96854 q = 1) (hb : d97926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96854, d97926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12812 q ha hb
    | true =>
      simp only [d96854, d97926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12813 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d96784 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d96855 q = 1) (hb : d97927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96855, d97927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d96855, d97927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d96857 q = 1) (hb : d97879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96857, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12814 q ha hb
    | true =>
      simp only [d96857, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d96858 q = 1) (hb : d97928 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96858, d97928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d96858, d97928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d96859 q = 1) (hb : d97929 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96859, d97929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d96859, d97929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d96860 q = 1) (hb : d97930 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96860, d97930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d96860, d97930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d96861 q = 1) (hb : d97931 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96861, d97931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d96861, d97931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d96862 q = 1) (hb : d97932 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96862, d97932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96862, d97932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro12816 (p : Pattern) (ha : d96874 p = 1) (hb : d97934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96773 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96864 q = 1) (hb : d97870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96864, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12807 q ha hb
    | true =>
      simp only [d96864, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96865 q = 1) (hb : d97871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96865, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96865, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96866 q = 1) (hb : d97872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96866, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96866, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96867 q = 1) (hb : d97873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96867, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96867, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96868 q = 1) (hb : d97874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96868, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96868, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96873 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96874 q = 1) (hb : d97934 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96874, d97934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96874, d97934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro12817 (p : Pattern) (ha : d96887 p = 1) (hb : d97941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96854 q = 1) (hb : d97926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96854, d97926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12812 q ha hb
    | true =>
      simp only [d96854, d97926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12813 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96855 q = 1) (hb : d97927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96855, d97927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96855, d97927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96857 q = 1) (hb : d97879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96857, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12814 q ha hb
    | true =>
      simp only [d96857, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96858 q = 1) (hb : d97928 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96858, d97928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96858, d97928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96859 q = 1) (hb : d97929 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96859, d97929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96859, d97929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96885 q = 1) (hb : d97939 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96885, d97939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96885, d97939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96886 q = 1) (hb : d97940 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96886, d97940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96886, d97940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96887 q = 1) (hb : d97941 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96887, d97941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96887, d97941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12818 (p : Pattern) (ha : d6349 p = 1) (hb : d52883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h2 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1387 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1388 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h8 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1393 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1394 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1395 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1395, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1395, d52883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6349 q = 1) (hb : d52883 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12819 (p : Pattern) (ha : d13156 p = 1) (hb : d52877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1380 q = 1) (hb : d52868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d52868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
  have h2 (q : Pattern) (ha : d1100 q = 1) (hb : d52681 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro149 q ha hb
    | true =>
      simp only [d1100, d52681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1381 q = 1) (hb : d52869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1381, d52869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1101 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1101, d52682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1382 q = 1) (hb : d52870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1382, d52870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1383 q = 1) (hb : d52871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1383, d52871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1385 q = 1) (hb : d52873 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d52873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
  have h8 (q : Pattern) (ha : d1110 q = 1) (hb : d52691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro150 q ha hb
    | true =>
      simp only [d1110, d52691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1386 q = 1) (hb : d52874 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1386, d52874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1111 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1111, d52692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1387 q = 1) (hb : d52875 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1387, d52875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1388 q = 1) (hb : d52876 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1388, d52876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1389 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1389, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1389, d52877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13156 q = 1) (hb : d52877 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12820 (p : Pattern) (ha : d13190 p = 1) (hb : d52888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h2 (q : Pattern) (ha : d1121 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
    | true =>
      simp only [d1121, d52702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1392 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1392, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1122 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1122, d52703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1393 q = 1) (hb : d52881 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1393, d52881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1394 q = 1) (hb : d52882 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1394, d52882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1400 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1400, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1400, d52888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13190 q = 1) (hb : d52888 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12821 (p : Pattern) (ha : d96902 p = 1) (hb : d97950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96897 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13174 q = 1) (hb : d96895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13174, d96895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12819 q ha hb
    | true =>
      simp only [d13174, d96895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12818 q ha hb
  have h3 (q : Pattern) (ha : d13175 q = 1) (hb : d96896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13175, d96896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13175, d96896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13176 q = 1) (hb : d96897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13176, d96897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13176, d96897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96897 q = 1) (hb : d97947 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96900 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13191 q = 1) (hb : d96898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d96898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12818 q ha hb
    | true =>
      simp only [d13191, d96898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12820 q ha hb
  have h8 (q : Pattern) (ha : d13192 q = 1) (hb : d96899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d96899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13192, d96899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13193 q = 1) (hb : d96900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d96900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13193, d96900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96900 q = 1) (hb : d97948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d96901 q = 1) (hb : d97949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96901, d97949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96901, d97949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96902 q = 1) (hb : d97950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96902, d97950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96902, d97950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12822 (p : Pattern) (ha : d96912 p = 1) (hb : d97956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96903 q = 1) (hb : d97951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96903, d97951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12821 q ha hb
    | true =>
      simp only [d96903, d97951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96904 q = 1) (hb : d97952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96904, d97952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96904, d97952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96908 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96909 q = 1) (hb : d97953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96909, d97953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96909, d97953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96910 q = 1) (hb : d97954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96910, d97954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96910, d97954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96911 q = 1) (hb : d97955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96911, d97955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96911, d97955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96912 q = 1) (hb : d97956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96912, d97956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96912, d97956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12823 (p : Pattern) (ha : d96906 p = 1) (hb : d97958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13191 q = 1) (hb : d96898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d96898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12818 q ha hb
    | true =>
      simp only [d13191, d96898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12820 q ha hb
  have h3 (q : Pattern) (ha : d13192 q = 1) (hb : d96899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d96899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13192, d96899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13193 q = 1) (hb : d96900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d96900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13193, d96900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96900 q = 1) (hb : d97948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96905 q = 1) (hb : d97957 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96905, d97957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96905, d97957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d96906 q = 1) (hb : d97958 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96906, d97958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96906, d97958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12824 (p : Pattern) (ha : d96923 p = 1) (hb : d97964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96907 q = 1) (hb : d97959 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96907, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12823 q ha hb
    | true =>
      simp only [d96907, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96908 q = 1) (hb : d97960 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96908, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96908, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96919 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96920 q = 1) (hb : d97961 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96920, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96920, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96921 q = 1) (hb : d97962 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96921, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96921, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96922 q = 1) (hb : d97963 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96922, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96922, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96923 q = 1) (hb : d97964 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96923, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96923, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12825 (p : Pattern) (ha : d96926 p = 1) (hb : d97958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13191 q = 1) (hb : d96898 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13191, d96898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12818 q ha hb
    | true =>
      simp only [d13191, d96898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12820 q ha hb
  have h3 (q : Pattern) (ha : d13192 q = 1) (hb : d96899 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13192, d96899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13192, d96899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13193 q = 1) (hb : d96900 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13193, d96900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13193, d96900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96900 q = 1) (hb : d97948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96915 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96925 q = 1) (hb : d97957 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96925, d97957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96925, d97957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96926 q = 1) (hb : d97958 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96926, d97958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96926, d97958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12826 (p : Pattern) (ha : d96942 p = 1) (hb : d97964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96927 q = 1) (hb : d97959 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96927, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12825 q ha hb
    | true =>
      simp only [d96927, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96928 q = 1) (hb : d97960 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96928, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96928, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96939 q = 1) (hb : d97961 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96939, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96939, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d96940 q = 1) (hb : d97962 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96940, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96940, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96941 q = 1) (hb : d97963 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96941, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96941, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96942 q = 1) (hb : d97964 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96942, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96942, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12827 (p : Pattern) (ha : d96948 p = 1) (hb : d97972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96924 q = 1) (hb : d97965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96924, d97965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12822 q ha hb
    | true =>
      simp only [d96924, d97965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12824 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96937 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96938 q = 1) (hb : d97966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96938, d97966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96938, d97966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96943 q = 1) (hb : d97967 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96943, d97967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12826 q ha hb
    | true =>
      simp only [d96943, d97967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96944 q = 1) (hb : d97968 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96944, d97968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96944, d97968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96945 q = 1) (hb : d97969 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96945, d97969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96945, d97969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96946 q = 1) (hb : d97970 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96946, d97970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96946, d97970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96947 q = 1) (hb : d97971 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96947, d97971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96947, d97971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96948 q = 1) (hb : d97972 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96948, d97972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96948, d97972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12828 (p : Pattern) (ha : d96961 p = 1) (hb : d97978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96780 q = 1) (hb : d97876 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96780, d97876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96780, d97876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12798 q ha hb
  have h2 (q : Pattern) (ha : d96781 q = 1) (hb : d97877 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96781, d97877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96781, d97877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96790 q = 1) (hb : d97885 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96790, d97885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12798 q ha hb
    | true =>
      simp only [d96790, d97885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12800 q ha hb
  have h4 (q : Pattern) (ha : d96791 q = 1) (hb : d97886 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96791, d97886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96791, d97886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96792 q = 1) (hb : d97887 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96792, d97887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96792, d97887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96863 q = 1) (hb : d97933 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96863, d97933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12809 q ha hb
    | true =>
      simp only [d96863, d97933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12815 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96880 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96881 q = 1) (hb : d97935 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96881, d97935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12816 q ha hb
    | true =>
      simp only [d96881, d97935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96882 q = 1) (hb : d97936 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96882, d97936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96882, d97936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96883 q = 1) (hb : d97937 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96883, d97937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96883, d97937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d96884 q = 1) (hb : d97938 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96884, d97938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96884, d97938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96888 q = 1) (hb : d97942 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96888, d97942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96888, d97942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12817 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d96890 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d96891 q = 1) (hb : d97943 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96891, d97943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96891, d97943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d96892 q = 1) (hb : d97944 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96892, d97944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d96892, d97944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d96893 q = 1) (hb : d97945 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96893, d97945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96893, d97945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d96894 q = 1) (hb : d97946 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96894, d97946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96894, d97946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96949 q = 1) (hb : d97973 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96949, d97973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96949, d97973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12827 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d96956 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d96957 q = 1) (hb : d97974 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96957, d97974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d96957, d97974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d96958 q = 1) (hb : d97975 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96958, d97975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d96958, d97975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d96959 q = 1) (hb : d97976 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96959, d97976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d96959, d97976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d96960 q = 1) (hb : d97977 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96960, d97977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d96960, d97977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d96961 q = 1) (hb : d97978 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96961, d97978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96961, d97978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro12829 (p : Pattern) (ha : d96967 p = 1) (hb : d97984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96962 q = 1) (hb : d97979 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96962, d97979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96962, d97979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12828 q ha hb
  have h2 (q : Pattern) (ha : d96963 q = 1) (hb : d97980 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96963, d97980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96963, d97980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96964 q = 1) (hb : d97981 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96964, d97981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96964, d97981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96965 q = 1) (hb : d97982 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96965, d97982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96965, d97982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96966 q = 1) (hb : d97983 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96966, d97983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96966, d97983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96967 q = 1) (hb : d97984 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96967, d97984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96967, d97984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12830 (p : Pattern) (ha : d5120 p = 1) (hb : d53027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1584 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1585 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1586 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1586, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1586, d53027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5120 q = 1) (hb : d53027 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12831 (p : Pattern) (ha : d13287 p = 1) (hb : d53029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1584 q = 1) (hb : d53025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1584, d53025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1585 q = 1) (hb : d53026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1585, d53026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1588 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d53029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13287 q = 1) (hb : d53029 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12832 (p : Pattern) (ha : d96978 p = 1) (hb : d97990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96973 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13288 q = 1) (hb : d96971 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d96971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12830 q ha hb
    | true =>
      simp only [d13288, d96971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12831 q ha hb
  have h3 (q : Pattern) (ha : d13289 q = 1) (hb : d96972 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d96972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13289, d96972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13290 q = 1) (hb : d96973 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d96973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13290, d96973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96973 q = 1) (hb : d97988 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96976 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96977 q = 1) (hb : d97989 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96977, d97989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96977, d97989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96978 q = 1) (hb : d97990 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96978, d97990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96978, d97990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12833 (p : Pattern) (ha : d96988 p = 1) (hb : d97996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96979 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12832 q ha hb
    | true =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96980 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96984 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96985 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96986 q = 1) (hb : d97994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96986, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96986, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96987 q = 1) (hb : d97995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96987, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96987, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96988 q = 1) (hb : d97996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96988, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96988, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12834 (p : Pattern) (ha : d96998 p = 1) (hb : d98002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96992 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96993 q = 1) (hb : d97997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96993, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12833 q ha hb
    | true =>
      simp only [d96993, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96994 q = 1) (hb : d97998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96994, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96994, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96995 q = 1) (hb : d97999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96995, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96995, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96996 q = 1) (hb : d98000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96996, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96996, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96997 q = 1) (hb : d98001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96997, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96997, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96998 q = 1) (hb : d98002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96998, d98002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96998, d98002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12835 (p : Pattern) (ha : d97001 p = 1) (hb : d98005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96979 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12832 q ha hb
    | true =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96980 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96984 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96985 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96986 q = 1) (hb : d97994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96986, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96986, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96987 q = 1) (hb : d97995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96987, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96987, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97001 q = 1) (hb : d98005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97001, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97001, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12836 (p : Pattern) (ha : d97008 p = 1) (hb : d98011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96992 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96993 q = 1) (hb : d97997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96993, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12833 q ha hb
    | true =>
      simp only [d96993, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d96994 q = 1) (hb : d97998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96994, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96994, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96995 q = 1) (hb : d97999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96995, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96995, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96996 q = 1) (hb : d98000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96996, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96996, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96997 q = 1) (hb : d98001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96997, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96997, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d97002 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d97003 q = 1) (hb : d98006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97003, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12835 q ha hb
    | true =>
      simp only [d97003, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d97004 q = 1) (hb : d98007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97004, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97004, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97005 q = 1) (hb : d98008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97005, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97005, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d97006 q = 1) (hb : d98009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97006, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97006, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d97007 q = 1) (hb : d98010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97007, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97007, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d97008 q = 1) (hb : d98011 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97008, d98011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97008, d98011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12837 (p : Pattern) (ha : d97013 p = 1) (hb : d98016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96979 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12832 q ha hb
    | true =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96980 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96984 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96985 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96986 q = 1) (hb : d97994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96986, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96986, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97012 q = 1) (hb : d98015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97012, d98015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97012, d98015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97013 q = 1) (hb : d98016 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97013, d98016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97013, d98016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12838 (p : Pattern) (ha : d97022 p = 1) (hb : d98023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96979 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12832 q ha hb
    | true =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96980 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96984 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96985 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97020 q = 1) (hb : d98021 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97020, d98021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97020, d98021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97021 q = 1) (hb : d98022 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97021, d98022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97021, d98022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97022 q = 1) (hb : d98023 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97022, d98023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97022, d98023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12839 (p : Pattern) (ha : d13282 p = 1) (hb : d53015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1555 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro205 q ha hb
    | true =>
      simp only [d1555, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1556 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1556, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1557 q = 1) (hb : d52998 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1557, d52998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1558 q = 1) (hb : d52999 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1558, d52999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1572 q = 1) (hb : d53013 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1572, d53013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1573 q = 1) (hb : d53014 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1573, d53014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1574 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1574, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1574, d53015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13282 q = 1) (hb : d53015 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12840 (p : Pattern) (ha : d97033 p = 1) (hb : d98029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97031 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13283 q = 1) (hb : d97029 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13283, d97029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12839 q ha hb
    | true =>
      simp only [d13283, d97029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12830 q ha hb
  have h3 (q : Pattern) (ha : d13284 q = 1) (hb : d97030 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13284, d97030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13284, d97030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13285 q = 1) (hb : d97031 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13285, d97031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13285, d97031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97031 q = 1) (hb : d98027 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96973 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13288 q = 1) (hb : d96971 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d96971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12830 q ha hb
    | true =>
      simp only [d13288, d96971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12831 q ha hb
  have h8 (q : Pattern) (ha : d13289 q = 1) (hb : d96972 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d96972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13289, d96972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13290 q = 1) (hb : d96973 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d96973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13290, d96973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96973 q = 1) (hb : d97988 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d97032 q = 1) (hb : d98028 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97032, d98028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97032, d98028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d97033 q = 1) (hb : d98029 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97033, d98029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d97033, d98029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12841 (p : Pattern) (ha : d97043 p = 1) (hb : d98035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97034 q = 1) (hb : d98030 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97034, d98030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12840 q ha hb
    | true =>
      simp only [d97034, d98030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97035 q = 1) (hb : d98031 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97035, d98031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97035, d98031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97039 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97040 q = 1) (hb : d98032 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97040, d98032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97040, d98032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97041 q = 1) (hb : d98033 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97041, d98033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97041, d98033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97042 q = 1) (hb : d98034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97042, d98034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97042, d98034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97043 q = 1) (hb : d98035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97043, d98035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97043, d98035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12842 (p : Pattern) (ha : d97037 p = 1) (hb : d97990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96973 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13288 q = 1) (hb : d96971 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13288, d96971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12830 q ha hb
    | true =>
      simp only [d13288, d96971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12831 q ha hb
  have h3 (q : Pattern) (ha : d13289 q = 1) (hb : d96972 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13289, d96972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13289, d96972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13290 q = 1) (hb : d96973 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13290, d96973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13290, d96973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96973 q = 1) (hb : d97988 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d97036 q = 1) (hb : d97989 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97036, d97989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97036, d97989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d97037 q = 1) (hb : d97990 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97037, d97990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97037, d97990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12843 (p : Pattern) (ha : d97047 p = 1) (hb : d97996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97038 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97038, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12842 q ha hb
    | true =>
      simp only [d97038, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97039 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97039, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97039, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96984 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97044 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97044, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97044, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97045 q = 1) (hb : d97994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97045, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97045, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97046 q = 1) (hb : d97995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97046, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97046, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97047 q = 1) (hb : d97996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97047, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97047, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12844 (p : Pattern) (ha : d97053 p = 1) (hb : d97996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96979 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12832 q ha hb
    | true =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96980 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97050 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97050, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97050, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97051 q = 1) (hb : d97994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97051, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97051, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97052 q = 1) (hb : d97995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97052, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97052, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97053 q = 1) (hb : d97996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97053, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97053, d97996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12845 (p : Pattern) (ha : d97059 p = 1) (hb : d98042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97015 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d97016 q = 1) (hb : d98017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97016, d98017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12837 q ha hb
    | true =>
      simp only [d97016, d98017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d97017 q = 1) (hb : d98018 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97017, d98018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97017, d98018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97018 q = 1) (hb : d98019 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97018, d98019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97018, d98019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97019 q = 1) (hb : d98020 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97019, d98020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97019, d98020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97025 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97026 q = 1) (hb : d98024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97026, d98024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12838 q ha hb
    | true =>
      simp only [d97026, d98024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97027 q = 1) (hb : d98025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97027, d98025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97027, d98025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97028 q = 1) (hb : d98026 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97028, d98026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d97028, d98026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d97048 q = 1) (hb : d98036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97048, d98036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12841 q ha hb
    | true =>
      simp only [d97048, d98036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12843 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96993 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d97049 q = 1) (hb : d98037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97049, d98037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97049, d98037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d97054 q = 1) (hb : d97997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97054, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12844 q ha hb
    | true =>
      simp only [d97054, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d97055 q = 1) (hb : d98038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97055, d98038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d97055, d98038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d97056 q = 1) (hb : d98039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97056, d98039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d97056, d98039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d97057 q = 1) (hb : d98040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97057, d98040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97057, d98040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d97058 q = 1) (hb : d98041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97058, d98041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97058, d98041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d97059 q = 1) (hb : d98042 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97059, d98042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97059, d98042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro12846 (p : Pattern) (ha : d97060 p = 1) (hb : d98043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96979 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12832 q ha hb
    | true =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96980 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96984 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96985 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96986 q = 1) (hb : d97994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96986, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96986, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97012 q = 1) (hb : d98015 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97012, d98015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97012, d98015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97060 q = 1) (hb : d98043 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97060, d98043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97060, d98043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12847 (p : Pattern) (ha : d97066 p = 1) (hb : d98048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96979 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12832 q ha hb
    | true =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96980 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96984 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96985 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96985, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97020 q = 1) (hb : d98021 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97020, d98021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97020, d98021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97021 q = 1) (hb : d98022 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97021, d98022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97021, d98022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97066 q = 1) (hb : d98048 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97066, d98048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97066, d98048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12848 (p : Pattern) (ha : d97071 p = 1) (hb : d98052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97034 q = 1) (hb : d98030 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97034, d98030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12840 q ha hb
    | true =>
      simp only [d97034, d98030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97035 q = 1) (hb : d98031 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97035, d98031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97035, d98031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97039 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97040 q = 1) (hb : d98032 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97040, d98032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97040, d98032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97041 q = 1) (hb : d98033 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97041, d98033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97041, d98033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97042 q = 1) (hb : d98034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97042, d98034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97042, d98034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97071 q = 1) (hb : d98052 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97071, d98052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97071, d98052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12849 (p : Pattern) (ha : d97072 p = 1) (hb : d98005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97038 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97038, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12842 q ha hb
    | true =>
      simp only [d97038, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97039 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97039, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97039, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96984 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97044 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97044, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97044, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97045 q = 1) (hb : d97994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97045, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97045, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97046 q = 1) (hb : d97995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97046, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97046, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97072 q = 1) (hb : d98005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97072, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97072, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12850 (p : Pattern) (ha : d97075 p = 1) (hb : d98005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96979 q = 1) (hb : d97991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12832 q ha hb
    | true =>
      simp only [d96979, d97991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96980 q = 1) (hb : d97992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96980, d97992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97050 q = 1) (hb : d97993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97050, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97050, d97993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97051 q = 1) (hb : d97994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97051, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97051, d97994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97052 q = 1) (hb : d97995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97052, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97052, d97995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97075 q = 1) (hb : d98005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97075, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97075, d98005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12851 (p : Pattern) (ha : d97081 p = 1) (hb : d98059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97015 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d97016 q = 1) (hb : d98017 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97016, d98017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12837 q ha hb
    | true =>
      simp only [d97016, d98017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d97017 q = 1) (hb : d98018 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97017, d98018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97017, d98018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97018 q = 1) (hb : d98019 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97018, d98019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97018, d98019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97019 q = 1) (hb : d98020 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97019, d98020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97019, d98020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97025 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97026 q = 1) (hb : d98024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97026, d98024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12838 q ha hb
    | true =>
      simp only [d97026, d98024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97027 q = 1) (hb : d98025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97027, d98025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97027, d98025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97028 q = 1) (hb : d98026 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97028, d98026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d97028, d98026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d97048 q = 1) (hb : d98036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97048, d98036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12841 q ha hb
    | true =>
      simp only [d97048, d98036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12843 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96993 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d97049 q = 1) (hb : d98037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97049, d98037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97049, d98037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d97054 q = 1) (hb : d97997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97054, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12844 q ha hb
    | true =>
      simp only [d97054, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d97055 q = 1) (hb : d98038 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97055, d98038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d97055, d98038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d97056 q = 1) (hb : d98039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97056, d98039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d97056, d98039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d97057 q = 1) (hb : d98040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97057, d98040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97057, d98040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d97058 q = 1) (hb : d98041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97058, d98041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97058, d98041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d97061 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d97062 q = 1) (hb : d98044 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97062, d98044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12846 q ha hb
    | true =>
      simp only [d97062, d98044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d97063 q = 1) (hb : d98045 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97063, d98045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97063, d98045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d97064 q = 1) (hb : d98046 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97064, d98046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d97064, d98046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d97065 q = 1) (hb : d98047 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97065, d98047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97065, d98047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d97067 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d97068 q = 1) (hb : d98049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97068, d98049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12847 q ha hb
    | true =>
      simp only [d97068, d98049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d97069 q = 1) (hb : d98050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97069, d98050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97069, d98050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d97070 q = 1) (hb : d98051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97070, d98051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d97070, d98051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d97073 q = 1) (hb : d98053 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97073, d98053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12848 q ha hb
    | true =>
      simp only [d97073, d98053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12849 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d97003 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d97074 q = 1) (hb : d98054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97074, d98054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d97074, d98054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d97076 q = 1) (hb : d98006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97076, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12850 q ha hb
    | true =>
      simp only [d97076, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d97077 q = 1) (hb : d98055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97077, d98055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d97077, d98055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d97078 q = 1) (hb : d98056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97078, d98056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d97078, d98056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d97079 q = 1) (hb : d98057 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97079, d98057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d97079, d98057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d97080 q = 1) (hb : d98058 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97080, d98058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d97080, d98058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d97081 q = 1) (hb : d98059 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97081, d98059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d97081, d98059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro12852 (p : Pattern) (ha : d97093 p = 1) (hb : d98061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96992 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d97083 q = 1) (hb : d97997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97083, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12843 q ha hb
    | true =>
      simp only [d97083, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d97084 q = 1) (hb : d97998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97084, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97084, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97085 q = 1) (hb : d97999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97085, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97085, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97086 q = 1) (hb : d98000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97086, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97086, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97087 q = 1) (hb : d98001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97087, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97087, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d97092 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d97093 q = 1) (hb : d98061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97093, d98061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97093, d98061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro12853 (p : Pattern) (ha : d97106 p = 1) (hb : d98068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97073 q = 1) (hb : d98053 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97073, d98053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12848 q ha hb
    | true =>
      simp only [d97073, d98053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12849 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97003 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97074 q = 1) (hb : d98054 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97074, d98054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97074, d98054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d97076 q = 1) (hb : d98006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97076, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12850 q ha hb
    | true =>
      simp only [d97076, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97077 q = 1) (hb : d98055 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97077, d98055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97077, d98055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97078 q = 1) (hb : d98056 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97078, d98056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97078, d98056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97104 q = 1) (hb : d98066 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97104, d98066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97104, d98066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97105 q = 1) (hb : d98067 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97105, d98067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97105, d98067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97106 q = 1) (hb : d98068 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97106, d98068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97106, d98068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12854 (p : Pattern) (ha : d6495 p = 1) (hb : d53198 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h8 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1869 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1870 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1871 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1872 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1872, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1872, d53198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6495 q = 1) (hb : d53198 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12855 (p : Pattern) (ha : d13482 p = 1) (hb : d53192 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d1862 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
  have h8 (q : Pattern) (ha : d1570 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro208 q ha hb
    | true =>
      simp only [d1570, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1863 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1863, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1571 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1571, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1864 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1864, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1865 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1865, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1866 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1866, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1866, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13482 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12856 (p : Pattern) (ha : d13516 p = 1) (hb : d53203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1868 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
  have h2 (q : Pattern) (ha : d1582 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro209 q ha hb
    | true =>
      simp only [d1582, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1869 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1869, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1583 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1583, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1870 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1870, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1871 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1877 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13516 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12857 (p : Pattern) (ha : d97121 p = 1) (hb : d98077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97116 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13500 q = 1) (hb : d97114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13500, d97114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12855 q ha hb
    | true =>
      simp only [d13500, d97114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12854 q ha hb
  have h3 (q : Pattern) (ha : d13501 q = 1) (hb : d97115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13501, d97115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13501, d97115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13502 q = 1) (hb : d97116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13502, d97116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13502, d97116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97116 q = 1) (hb : d98074 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97119 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13517 q = 1) (hb : d97117 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d97117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12854 q ha hb
    | true =>
      simp only [d13517, d97117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12856 q ha hb
  have h8 (q : Pattern) (ha : d13518 q = 1) (hb : d97118 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d97118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13518, d97118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13519 q = 1) (hb : d97119 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d97119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13519, d97119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97119 q = 1) (hb : d98075 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d97120 q = 1) (hb : d98076 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97120, d98076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97120, d98076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d97121 q = 1) (hb : d98077 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97121, d98077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d97121, d98077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12858 (p : Pattern) (ha : d97131 p = 1) (hb : d98083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97122 q = 1) (hb : d98078 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97122, d98078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12857 q ha hb
    | true =>
      simp only [d97122, d98078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97123 q = 1) (hb : d98079 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97123, d98079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97123, d98079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97127 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97128 q = 1) (hb : d98080 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97128, d98080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97128, d98080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97129 q = 1) (hb : d98081 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97129, d98081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97129, d98081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97130 q = 1) (hb : d98082 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97130, d98082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97130, d98082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97131 q = 1) (hb : d98083 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97131, d98083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97131, d98083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12859 (p : Pattern) (ha : d97125 p = 1) (hb : d98085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97119 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13517 q = 1) (hb : d97117 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d97117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12854 q ha hb
    | true =>
      simp only [d13517, d97117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12856 q ha hb
  have h3 (q : Pattern) (ha : d13518 q = 1) (hb : d97118 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d97118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13518, d97118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13519 q = 1) (hb : d97119 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d97119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13519, d97119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97119 q = 1) (hb : d98075 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d97124 q = 1) (hb : d98084 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97124, d98084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97124, d98084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d97125 q = 1) (hb : d98085 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97125, d98085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97125, d98085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12860 (p : Pattern) (ha : d97142 p = 1) (hb : d98091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97126 q = 1) (hb : d98086 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97126, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12859 q ha hb
    | true =>
      simp only [d97126, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97127 q = 1) (hb : d98087 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97127, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97127, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97138 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97139 q = 1) (hb : d98088 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97139, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97139, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97140 q = 1) (hb : d98089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97140, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97140, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97141 q = 1) (hb : d98090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97141, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97141, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97142 q = 1) (hb : d98091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97142, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97142, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12861 (p : Pattern) (ha : d97145 p = 1) (hb : d98085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97119 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13517 q = 1) (hb : d97117 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13517, d97117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12854 q ha hb
    | true =>
      simp only [d13517, d97117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12856 q ha hb
  have h3 (q : Pattern) (ha : d13518 q = 1) (hb : d97118 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13518, d97118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13518, d97118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13519 q = 1) (hb : d97119 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13519, d97119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13519, d97119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97119 q = 1) (hb : d98075 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97134 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97144 q = 1) (hb : d98084 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97144, d98084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97144, d98084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97145 q = 1) (hb : d98085 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97145, d98085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d97145, d98085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12862 (p : Pattern) (ha : d97161 p = 1) (hb : d98091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97146 q = 1) (hb : d98086 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97146, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12861 q ha hb
    | true =>
      simp only [d97146, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97147 q = 1) (hb : d98087 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97147, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97147, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97158 q = 1) (hb : d98088 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97158, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97158, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97159 q = 1) (hb : d98089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97159, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97159, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97160 q = 1) (hb : d98090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97160, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97160, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97161 q = 1) (hb : d98091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97161, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97161, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12863 (p : Pattern) (ha : d97167 p = 1) (hb : d98099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97143 q = 1) (hb : d98092 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97143, d98092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12858 q ha hb
    | true =>
      simp only [d97143, d98092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12860 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97156 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97157 q = 1) (hb : d98093 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97157, d98093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97157, d98093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d97162 q = 1) (hb : d98094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97162, d98094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12862 q ha hb
    | true =>
      simp only [d97162, d98094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97163 q = 1) (hb : d98095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97163, d98095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97163, d98095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97164 q = 1) (hb : d98096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97164, d98096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97164, d98096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97165 q = 1) (hb : d98097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97165, d98097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97165, d98097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97166 q = 1) (hb : d98098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97166, d98098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97166, d98098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97167 q = 1) (hb : d98099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97167, d98099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97167, d98099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12864 (p : Pattern) (ha : d97180 p = 1) (hb : d98105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96999 q = 1) (hb : d98003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96999, d98003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96999, d98003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12834 q ha hb
  have h2 (q : Pattern) (ha : d97000 q = 1) (hb : d98004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97000, d98004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97000, d98004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97009 q = 1) (hb : d98012 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97009, d98012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12834 q ha hb
    | true =>
      simp only [d97009, d98012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12836 q ha hb
  have h4 (q : Pattern) (ha : d97010 q = 1) (hb : d98013 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97010, d98013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97010, d98013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97011 q = 1) (hb : d98014 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97011, d98014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97011, d98014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97082 q = 1) (hb : d98060 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97082, d98060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12845 q ha hb
    | true =>
      simp only [d97082, d98060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12851 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d97099 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d97100 q = 1) (hb : d98062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97100, d98062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12852 q ha hb
    | true =>
      simp only [d97100, d98062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d97101 q = 1) (hb : d98063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97101, d98063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97101, d98063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97102 q = 1) (hb : d98064 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97102, d98064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97102, d98064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d97103 q = 1) (hb : d98065 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97103, d98065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97103, d98065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d97107 q = 1) (hb : d98069 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97107, d98069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97107, d98069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12853 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d97109 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d97110 q = 1) (hb : d98070 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97110, d98070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d97110, d98070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d97111 q = 1) (hb : d98071 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97111, d98071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d97111, d98071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d97112 q = 1) (hb : d98072 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97112, d98072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d97112, d98072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d97113 q = 1) (hb : d98073 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d97113, d98073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d97113, d98073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d97168 q = 1) (hb : d98100 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97168, d98100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97168, d98100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12863 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d97175 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d97176 q = 1) (hb : d98101 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97176, d98101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d97176, d98101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d97177 q = 1) (hb : d98102 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97177, d98102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d97177, d98102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d97178 q = 1) (hb : d98103 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97178, d98103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d97178, d98103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d97179 q = 1) (hb : d98104 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d97179, d98104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d97179, d98104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d97180 q = 1) (hb : d98105 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d97180, d98105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d97180, d98105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro12865 (p : Pattern) (ha : d97186 p = 1) (hb : d98111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97181 q = 1) (hb : d98106 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d97181, d98106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97181, d98106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12864 q ha hb
  have h2 (q : Pattern) (ha : d97182 q = 1) (hb : d98107 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97182, d98107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97182, d98107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97183 q = 1) (hb : d98108 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d97183, d98108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97183, d98108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97184 q = 1) (hb : d98109 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d97184, d98109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97184, d98109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97185 q = 1) (hb : d98110 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d97185, d98110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97185, d98110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97186 q = 1) (hb : d98111 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d97186, d98111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97186, d98111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12866 (p : Pattern) (ha : d5237 p = 1) (hb : d53348 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2067 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2068 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2069 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2069, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d5237 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d5237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12867 (p : Pattern) (ha : d13614 p = 1) (hb : d53350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2067 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2068 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2071 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13614 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12868 (p : Pattern) (ha : d97198 p = 1) (hb : d98118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97193 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13615 q = 1) (hb : d97191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d97191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12866 q ha hb
    | true =>
      simp only [d13615, d97191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12867 q ha hb
  have h3 (q : Pattern) (ha : d13616 q = 1) (hb : d97192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d97192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13616, d97192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13617 q = 1) (hb : d97193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d97193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13617, d97193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97193 q = 1) (hb : d98116 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97196 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97197 q = 1) (hb : d98117 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97197, d98117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97197, d98117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97198 q = 1) (hb : d98118 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97198, d98118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d97198, d98118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12869 (p : Pattern) (ha : d97208 p = 1) (hb : d98124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97199 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12868 q ha hb
    | true =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97200 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97205 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97206 q = 1) (hb : d98122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97206, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97206, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97207 q = 1) (hb : d98123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97207, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97207, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97208 q = 1) (hb : d98124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97208, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97208, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12870 (p : Pattern) (ha : d97218 p = 1) (hb : d98130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97212 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d97213 q = 1) (hb : d98125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97213, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12869 q ha hb
    | true =>
      simp only [d97213, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d97214 q = 1) (hb : d98126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97214, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97214, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97215 q = 1) (hb : d98127 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97215, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97215, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97216 q = 1) (hb : d98128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97216, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97216, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97217 q = 1) (hb : d98129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97217, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97217, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97218 q = 1) (hb : d98130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97218, d98130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97218, d98130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12871 (p : Pattern) (ha : d97221 p = 1) (hb : d98133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97199 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12868 q ha hb
    | true =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97200 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97205 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97206 q = 1) (hb : d98122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97206, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97206, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97207 q = 1) (hb : d98123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97207, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97207, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97221 q = 1) (hb : d98133 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97221, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97221, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12872 (p : Pattern) (ha : d97228 p = 1) (hb : d98139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97212 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d97213 q = 1) (hb : d98125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97213, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12869 q ha hb
    | true =>
      simp only [d97213, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d97214 q = 1) (hb : d98126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97214, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97214, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97215 q = 1) (hb : d98127 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97215, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97215, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97216 q = 1) (hb : d98128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97216, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97216, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97217 q = 1) (hb : d98129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97217, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97217, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d97222 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d97223 q = 1) (hb : d98134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97223, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12871 q ha hb
    | true =>
      simp only [d97223, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d97224 q = 1) (hb : d98135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97224, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97224, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97225 q = 1) (hb : d98136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97225, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97225, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d97226 q = 1) (hb : d98137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97226, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97226, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d97227 q = 1) (hb : d98138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97227, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97227, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d97228 q = 1) (hb : d98139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97228, d98139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97228, d98139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro12873 (p : Pattern) (ha : d97233 p = 1) (hb : d98144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97199 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12868 q ha hb
    | true =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97200 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97205 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97206 q = 1) (hb : d98122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97206, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97206, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97232 q = 1) (hb : d98143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97232, d98143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97232, d98143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97233 q = 1) (hb : d98144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97233, d98144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97233, d98144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12874 (p : Pattern) (ha : d97242 p = 1) (hb : d98151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97199 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12868 q ha hb
    | true =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97200 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97205 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97240 q = 1) (hb : d98149 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97240, d98149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97240, d98149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97241 q = 1) (hb : d98150 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97241, d98150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97241, d98150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97242 q = 1) (hb : d98151 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97242, d98151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97242, d98151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12875 (p : Pattern) (ha : d13609 p = 1) (hb : d53336 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2055 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2056 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2057 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2057, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d13609 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12876 (p : Pattern) (ha : d97253 p = 1) (hb : d98157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97251 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13610 q = 1) (hb : d97249 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13610, d97249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12875 q ha hb
    | true =>
      simp only [d13610, d97249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12866 q ha hb
  have h3 (q : Pattern) (ha : d13611 q = 1) (hb : d97250 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13611, d97250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13611, d97250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13612 q = 1) (hb : d97251 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13612, d97251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13612, d97251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97251 q = 1) (hb : d98155 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97193 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13615 q = 1) (hb : d97191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d97191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12866 q ha hb
    | true =>
      simp only [d13615, d97191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12867 q ha hb
  have h8 (q : Pattern) (ha : d13616 q = 1) (hb : d97192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d97192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13616, d97192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13617 q = 1) (hb : d97193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d97193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13617, d97193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97193 q = 1) (hb : d98116 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d97252 q = 1) (hb : d98156 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97252, d98156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97252, d98156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d97253 q = 1) (hb : d98157 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97253, d98157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d97253, d98157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12877 (p : Pattern) (ha : d97263 p = 1) (hb : d98163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97254 q = 1) (hb : d98158 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97254, d98158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12876 q ha hb
    | true =>
      simp only [d97254, d98158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97255 q = 1) (hb : d98159 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97255, d98159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97255, d98159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97259 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97260 q = 1) (hb : d98160 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97260, d98160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97260, d98160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97261 q = 1) (hb : d98161 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97261, d98161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97261, d98161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97262 q = 1) (hb : d98162 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97262, d98162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97262, d98162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97263 q = 1) (hb : d98163 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97263, d98163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97263, d98163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12878 (p : Pattern) (ha : d97257 p = 1) (hb : d98118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97193 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13615 q = 1) (hb : d97191 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13615, d97191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12866 q ha hb
    | true =>
      simp only [d13615, d97191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12867 q ha hb
  have h3 (q : Pattern) (ha : d13616 q = 1) (hb : d97192 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13616, d97192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13616, d97192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13617 q = 1) (hb : d97193 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13617, d97193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13617, d97193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97193 q = 1) (hb : d98116 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d97256 q = 1) (hb : d98117 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97256, d98117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97256, d98117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d97257 q = 1) (hb : d98118 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97257, d98118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97257, d98118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12879 (p : Pattern) (ha : d97267 p = 1) (hb : d98124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97258 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97258, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12878 q ha hb
    | true =>
      simp only [d97258, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97259 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97259, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97259, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97264 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97264, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97264, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97265 q = 1) (hb : d98122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97265, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97265, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97266 q = 1) (hb : d98123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97266, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97266, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97267 q = 1) (hb : d98124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97267, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97267, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12880 (p : Pattern) (ha : d97273 p = 1) (hb : d98124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97199 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12868 q ha hb
    | true =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97200 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97270 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97270, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97270, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97271 q = 1) (hb : d98122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97271, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97271, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97272 q = 1) (hb : d98123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97272, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97272, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97273 q = 1) (hb : d98124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97273, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97273, d98124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12881 (p : Pattern) (ha : d97279 p = 1) (hb : d98170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97235 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d97236 q = 1) (hb : d98145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97236, d98145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12873 q ha hb
    | true =>
      simp only [d97236, d98145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d97237 q = 1) (hb : d98146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97237, d98146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97237, d98146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97238 q = 1) (hb : d98147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97238, d98147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97238, d98147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97239 q = 1) (hb : d98148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97239, d98148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97239, d98148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97245 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97246 q = 1) (hb : d98152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97246, d98152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12874 q ha hb
    | true =>
      simp only [d97246, d98152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97247 q = 1) (hb : d98153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97247, d98153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97247, d98153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97248 q = 1) (hb : d98154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97248, d98154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d97248, d98154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d97268 q = 1) (hb : d98164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97268, d98164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12877 q ha hb
    | true =>
      simp only [d97268, d98164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12879 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d97213 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d97269 q = 1) (hb : d98165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97269, d98165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97269, d98165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d97274 q = 1) (hb : d98125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97274, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12880 q ha hb
    | true =>
      simp only [d97274, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d97275 q = 1) (hb : d98166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97275, d98166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d97275, d98166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d97276 q = 1) (hb : d98167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97276, d98167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d97276, d98167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d97277 q = 1) (hb : d98168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97277, d98168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97277, d98168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d97278 q = 1) (hb : d98169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97278, d98169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97278, d98169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d97279 q = 1) (hb : d98170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97279, d98170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97279, d98170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro12882 (p : Pattern) (ha : d97280 p = 1) (hb : d98171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97199 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12868 q ha hb
    | true =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97200 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97205 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97206 q = 1) (hb : d98122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97206, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97206, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97232 q = 1) (hb : d98143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97232, d98143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97232, d98143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97280 q = 1) (hb : d98171 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97280, d98171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97280, d98171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12883 (p : Pattern) (ha : d97286 p = 1) (hb : d98176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97199 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12868 q ha hb
    | true =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97200 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97205 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97205, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97240 q = 1) (hb : d98149 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97240, d98149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97240, d98149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97241 q = 1) (hb : d98150 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97241, d98150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97241, d98150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97286 q = 1) (hb : d98176 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97286, d98176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97286, d98176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12884 (p : Pattern) (ha : d97291 p = 1) (hb : d98180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97254 q = 1) (hb : d98158 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97254, d98158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12876 q ha hb
    | true =>
      simp only [d97254, d98158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97255 q = 1) (hb : d98159 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97255, d98159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97255, d98159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97259 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97260 q = 1) (hb : d98160 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97260, d98160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97260, d98160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97261 q = 1) (hb : d98161 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97261, d98161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97261, d98161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97262 q = 1) (hb : d98162 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97262, d98162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97262, d98162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97291 q = 1) (hb : d98180 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97291, d98180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97291, d98180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12885 (p : Pattern) (ha : d97292 p = 1) (hb : d98133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97258 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97258, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12878 q ha hb
    | true =>
      simp only [d97258, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97259 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97259, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97259, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97264 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97264, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97264, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97265 q = 1) (hb : d98122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97265, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97265, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97266 q = 1) (hb : d98123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97266, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97266, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97292 q = 1) (hb : d98133 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97292, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97292, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12886 (p : Pattern) (ha : d97295 p = 1) (hb : d98133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97199 q = 1) (hb : d98119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12868 q ha hb
    | true =>
      simp only [d97199, d98119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97200 q = 1) (hb : d98120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97200, d98120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97270 q = 1) (hb : d98121 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97270, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97270, d98121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97271 q = 1) (hb : d98122 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97271, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97271, d98122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97272 q = 1) (hb : d98123 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97272, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97272, d98123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97295 q = 1) (hb : d98133 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97295, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97295, d98133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12887 (p : Pattern) (ha : d97301 p = 1) (hb : d98187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97235 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d97236 q = 1) (hb : d98145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97236, d98145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12873 q ha hb
    | true =>
      simp only [d97236, d98145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d97237 q = 1) (hb : d98146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97237, d98146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97237, d98146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97238 q = 1) (hb : d98147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97238, d98147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97238, d98147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97239 q = 1) (hb : d98148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97239, d98148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97239, d98148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97245 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97246 q = 1) (hb : d98152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97246, d98152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12874 q ha hb
    | true =>
      simp only [d97246, d98152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97247 q = 1) (hb : d98153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97247, d98153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97247, d98153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97248 q = 1) (hb : d98154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97248, d98154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d97248, d98154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d97268 q = 1) (hb : d98164 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97268, d98164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12877 q ha hb
    | true =>
      simp only [d97268, d98164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12879 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d97213 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d97269 q = 1) (hb : d98165 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97269, d98165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97269, d98165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d97274 q = 1) (hb : d98125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97274, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12880 q ha hb
    | true =>
      simp only [d97274, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d97275 q = 1) (hb : d98166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97275, d98166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d97275, d98166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d97276 q = 1) (hb : d98167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97276, d98167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d97276, d98167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d97277 q = 1) (hb : d98168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97277, d98168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97277, d98168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d97278 q = 1) (hb : d98169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97278, d98169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97278, d98169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d97281 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d97282 q = 1) (hb : d98172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97282, d98172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12882 q ha hb
    | true =>
      simp only [d97282, d98172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d97283 q = 1) (hb : d98173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97283, d98173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97283, d98173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d97284 q = 1) (hb : d98174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97284, d98174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d97284, d98174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d97285 q = 1) (hb : d98175 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97285, d98175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97285, d98175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d97287 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d97288 q = 1) (hb : d98177 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97288, d98177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12883 q ha hb
    | true =>
      simp only [d97288, d98177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d97289 q = 1) (hb : d98178 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97289, d98178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97289, d98178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d97290 q = 1) (hb : d98179 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97290, d98179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d97290, d98179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d97293 q = 1) (hb : d98181 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97293, d98181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12884 q ha hb
    | true =>
      simp only [d97293, d98181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12885 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d97223 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d97294 q = 1) (hb : d98182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97294, d98182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d97294, d98182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d97296 q = 1) (hb : d98134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97296, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12886 q ha hb
    | true =>
      simp only [d97296, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d97297 q = 1) (hb : d98183 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97297, d98183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d97297, d98183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h32 (q : Pattern) (ha : d97298 q = 1) (hb : d98184 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97298, d98184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d97298, d98184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d97299 q = 1) (hb : d98185 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97299, d98185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d97299, d98185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  have h34 (q : Pattern) (ha : d97300 q = 1) (hb : d98186 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97300, d98186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d97300, d98186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d97301 q = 1) (hb : d98187 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97301, d98187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d97301, d98187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  exact h35 p ha hb
theorem andIntro12888 (p : Pattern) (ha : d97313 p = 1) (hb : d98189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97212 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d97303 q = 1) (hb : d98125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97303, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12879 q ha hb
    | true =>
      simp only [d97303, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d97304 q = 1) (hb : d98126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97304, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97304, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97305 q = 1) (hb : d98127 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97305, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97305, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97306 q = 1) (hb : d98128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97306, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97306, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97307 q = 1) (hb : d98129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97307, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97307, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d97312 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d97313 q = 1) (hb : d98189 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97313, d98189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97313, d98189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro12889 (p : Pattern) (ha : d97326 p = 1) (hb : d98196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97293 q = 1) (hb : d98181 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97293, d98181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12884 q ha hb
    | true =>
      simp only [d97293, d98181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12885 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97223 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97294 q = 1) (hb : d98182 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97294, d98182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97294, d98182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d97296 q = 1) (hb : d98134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97296, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12886 q ha hb
    | true =>
      simp only [d97296, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97297 q = 1) (hb : d98183 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97297, d98183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97297, d98183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97298 q = 1) (hb : d98184 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97298, d98184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97298, d98184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97324 q = 1) (hb : d98194 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97324, d98194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97324, d98194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97325 q = 1) (hb : d98195 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97325, d98195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97325, d98195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97326 q = 1) (hb : d98196 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97326, d98196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97326, d98196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12890 (p : Pattern) (ha : d6642 p = 1) (hb : d53515 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h8 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2348 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2349 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2350 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2350, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d6642 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d6642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d6642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12891 (p : Pattern) (ha : d13809 p = 1) (hb : d53509 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d2340 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
  have h8 (q : Pattern) (ha : d2053 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro267 q ha hb
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2341 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2054 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2342 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2343 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2344 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2344, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d13809 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12892 (p : Pattern) (ha : d13843 p = 1) (hb : d53520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2346 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
  have h2 (q : Pattern) (ha : d2065 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro268 q ha hb
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2347 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2066 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2348 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2349 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2355 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d13843 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12893 (p : Pattern) (ha : d97341 p = 1) (hb : d98205 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97336 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13827 q = 1) (hb : d97334 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13827, d97334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12891 q ha hb
    | true =>
      simp only [d13827, d97334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12890 q ha hb
  have h3 (q : Pattern) (ha : d13828 q = 1) (hb : d97335 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13828, d97335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13828, d97335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13829 q = 1) (hb : d97336 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13829, d97336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13829, d97336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97336 q = 1) (hb : d98202 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97339 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d13844 q = 1) (hb : d97337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d97337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12890 q ha hb
    | true =>
      simp only [d13844, d97337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12892 q ha hb
  have h8 (q : Pattern) (ha : d13845 q = 1) (hb : d97338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d97338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13845, d97338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13846 q = 1) (hb : d97339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d97339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13846, d97339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97339 q = 1) (hb : d98203 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d97340 q = 1) (hb : d98204 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97340, d98204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97340, d98204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d97341 q = 1) (hb : d98205 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97341, d98205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d97341, d98205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro12894 (p : Pattern) (ha : d97351 p = 1) (hb : d98211 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97342 q = 1) (hb : d98206 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97342, d98206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12893 q ha hb
    | true =>
      simp only [d97342, d98206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97343 q = 1) (hb : d98207 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97343, d98207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97343, d98207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97347 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97348 q = 1) (hb : d98208 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97348, d98208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97348, d98208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97349 q = 1) (hb : d98209 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97349, d98209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97349, d98209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97350 q = 1) (hb : d98210 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97350, d98210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97350, d98210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97351 q = 1) (hb : d98211 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97351, d98211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97351, d98211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12895 (p : Pattern) (ha : d97345 p = 1) (hb : d98213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97339 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13844 q = 1) (hb : d97337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d97337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12890 q ha hb
    | true =>
      simp only [d13844, d97337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12892 q ha hb
  have h3 (q : Pattern) (ha : d13845 q = 1) (hb : d97338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d97338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13845, d97338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13846 q = 1) (hb : d97339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d97339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13846, d97339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97339 q = 1) (hb : d98203 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d97344 q = 1) (hb : d98212 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97344, d98212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97344, d98212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d97345 q = 1) (hb : d98213 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97345, d98213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97345, d98213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro12896 (p : Pattern) (ha : d97362 p = 1) (hb : d98219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97346 q = 1) (hb : d98214 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97346, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12895 q ha hb
    | true =>
      simp only [d97346, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97347 q = 1) (hb : d98215 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97347, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97347, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97358 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97359 q = 1) (hb : d98216 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97359, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97359, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97360 q = 1) (hb : d98217 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97360, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97360, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97361 q = 1) (hb : d98218 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97361, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97361, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97362 q = 1) (hb : d98219 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97362, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97362, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12897 (p : Pattern) (ha : d97365 p = 1) (hb : d98213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97339 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13844 q = 1) (hb : d97337 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d13844, d97337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12890 q ha hb
    | true =>
      simp only [d13844, d97337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12892 q ha hb
  have h3 (q : Pattern) (ha : d13845 q = 1) (hb : d97338 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d13845, d97338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13845, d97338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13846 q = 1) (hb : d97339 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d13846, d97339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13846, d97339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97339 q = 1) (hb : d98203 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d98203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97354 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97364 q = 1) (hb : d98212 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d97364, d98212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97364, d98212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97365 q = 1) (hb : d98213 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d97365, d98213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d97365, d98213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h8 p ha hb
theorem andIntro12898 (p : Pattern) (ha : d97381 p = 1) (hb : d98219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97366 q = 1) (hb : d98214 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97366, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12897 q ha hb
    | true =>
      simp only [d97366, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97367 q = 1) (hb : d98215 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97367, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97367, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97378 q = 1) (hb : d98216 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97378, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97378, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97379 q = 1) (hb : d98217 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97379, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97379, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97380 q = 1) (hb : d98218 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97380, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97380, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97381 q = 1) (hb : d98219 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97381, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97381, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12899 (p : Pattern) (ha : d97387 p = 1) (hb : d98227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97363 q = 1) (hb : d98220 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97363, d98220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12894 q ha hb
    | true =>
      simp only [d97363, d98220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12896 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97377 q = 1) (hb : d98221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97377, d98221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97377, d98221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d97382 q = 1) (hb : d98222 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97382, d98222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12898 q ha hb
    | true =>
      simp only [d97382, d98222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97383 q = 1) (hb : d98223 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97383, d98223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97383, d98223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97384 q = 1) (hb : d98224 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97384, d98224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97384, d98224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97385 q = 1) (hb : d98225 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97385, d98225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97385, d98225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97386 q = 1) (hb : d98226 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97386, d98226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97386, d98226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97387 q = 1) (hb : d98227 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97387, d98227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97387, d98227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12900 (p : Pattern) (ha : d97400 p = 1) (hb : d98233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97219 q = 1) (hb : d98131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97219, d98131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97219, d98131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12870 q ha hb
  have h2 (q : Pattern) (ha : d97220 q = 1) (hb : d98132 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97220, d98132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97220, d98132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97229 q = 1) (hb : d98140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97229, d98140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12870 q ha hb
    | true =>
      simp only [d97229, d98140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12872 q ha hb
  have h4 (q : Pattern) (ha : d97230 q = 1) (hb : d98141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97230, d98141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97230, d98141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97231 q = 1) (hb : d98142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97231, d98142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97231, d98142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97302 q = 1) (hb : d98188 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97302, d98188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12881 q ha hb
    | true =>
      simp only [d97302, d98188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12887 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d97319 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d97320 q = 1) (hb : d98190 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97320, d98190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12888 q ha hb
    | true =>
      simp only [d97320, d98190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d97321 q = 1) (hb : d98191 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97321, d98191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97321, d98191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97322 q = 1) (hb : d98192 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97322, d98192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97322, d98192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d97323 q = 1) (hb : d98193 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97323, d98193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97323, d98193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d97327 q = 1) (hb : d98197 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97327, d98197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97327, d98197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12889 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d97329 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d97330 q = 1) (hb : d98198 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97330, d98198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d97330, d98198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d97331 q = 1) (hb : d98199 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97331, d98199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d97331, d98199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d97332 q = 1) (hb : d98200 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97332, d98200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d97332, d98200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d97333 q = 1) (hb : d98201 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d97333, d98201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d97333, d98201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d97388 q = 1) (hb : d98228 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97388, d98228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97388, d98228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12899 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d97395 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d97396 q = 1) (hb : d98229 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97396, d98229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d97396, d98229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d97397 q = 1) (hb : d98230 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97397, d98230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d97397, d98230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d97398 q = 1) (hb : d98231 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97398, d98231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d97398, d98231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d97399 q = 1) (hb : d98232 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d97399, d98232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d97399, d98232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d97400 q = 1) (hb : d98233 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d97400, d98233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d97400, d98233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro12901 (p : Pattern) (ha : d97406 p = 1) (hb : d98239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97401 q = 1) (hb : d98234 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d97401, d98234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97401, d98234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12900 q ha hb
  have h2 (q : Pattern) (ha : d97402 q = 1) (hb : d98235 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97402, d98235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97402, d98235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97403 q = 1) (hb : d98236 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d97403, d98236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97403, d98236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97404 q = 1) (hb : d98237 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d97404, d98237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97404, d98237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97405 q = 1) (hb : d98238 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d97405, d98238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97405, d98238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97406 q = 1) (hb : d98239 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d97406, d98239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97406, d98239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12902 (p : Pattern) (ha : d97412 p = 1) (hb : d98245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d96533 q = 1) (hb : d97734 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d96533, d97734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12725 q ha hb
    | true =>
      simp only [d96533, d97734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12757 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96750 q = 1) (hb : d97859 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d96750, d97859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96750, d97859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12793 q ha hb
  have h3 (q : Pattern) (ha : d96751 q = 1) (hb : d97860 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d96751, d97860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96751, d97860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96968 q = 1) (hb : d97985 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d96968, d97985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96968, d97985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12829 q ha hb
  have h5 (q : Pattern) (ha : d96969 q = 1) (hb : d97986 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d96969, d97986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96969, d97986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96970 q = 1) (hb : d97987 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d96970, d97987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96970, d97987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97187 q = 1) (hb : d98112 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d97187, d98112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97187, d98112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12865 q ha hb
  have h8 (q : Pattern) (ha : d97188 q = 1) (hb : d98113 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d97188, d98113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97188, d98113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97189 q = 1) (hb : d98114 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d97189, d98114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97189, d98114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97190 q = 1) (hb : d98115 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d97190, d98115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97190, d98115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d97407 q = 1) (hb : d98240 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d97407, d98240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97407, d98240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12901 q ha hb
  have h12 (q : Pattern) (ha : d97408 q = 1) (hb : d98241 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d97408, d98241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97408, d98241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d97409 q = 1) (hb : d98242 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d97409, d98242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97409, d98242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d97410 q = 1) (hb : d98243 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d97410, d98243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97410, d98243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d97411 q = 1) (hb : d98244 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d97411, d98244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97411, d98244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d97412 q = 1) (hb : d98245 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d97412, d98245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d97412, d98245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro12903 (p : Pattern) (ha : d97418 p = 1) (hb : d98251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97413 q = 1) (hb : d98246 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d97413, d98246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12902 q ha hb
    | true =>
      simp only [d97413, d98246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97414 q = 1) (hb : d98247 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d97414, d98247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97414, d98247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97415 q = 1) (hb : d98248 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d97415, d98248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97415, d98248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97416 q = 1) (hb : d98249 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d97416, d98249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97416, d98249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97417 q = 1) (hb : d98250 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d97417, d98250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97417, d98250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97418 q = 1) (hb : d98251 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d97418, d98251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97418, d98251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12904 (p : Pattern) (ha : d97424 p = 1) (hb : d98257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97419 q = 1) (hb : d98252 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d97419, d98252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12903 q ha hb
    | true =>
      simp only [d97419, d98252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97420 q = 1) (hb : d98253 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d97420, d98253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97420, d98253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97421 q = 1) (hb : d98254 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d97421, d98254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97421, d98254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97422 q = 1) (hb : d98255 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d97422, d98255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97422, d98255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97423 q = 1) (hb : d98256 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d97423, d98256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97423, d98256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97424 q = 1) (hb : d98257 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d97424, d98257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97424, d98257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12905 (p : Pattern) (ha : d97430 p = 1) (hb : d98263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97425 q = 1) (hb : d98258 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d97425, d98258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12904 q ha hb
    | true =>
      simp only [d97425, d98258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97426 q = 1) (hb : d98259 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d97426, d98259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97426, d98259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97427 q = 1) (hb : d98260 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d97427, d98260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97427, d98260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97428 q = 1) (hb : d98261 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d97428, d98261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97428, d98261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97429 q = 1) (hb : d98262 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d97429, d98262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97429, d98262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97430 q = 1) (hb : d98263 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d97430, d98263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97430, d98263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12906 (p : Pattern) (ha : d97436 p = 1) (hb : d98269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97431 q = 1) (hb : d98264 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d97431, d98264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12905 q ha hb
    | true =>
      simp only [d97431, d98264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97432 q = 1) (hb : d98265 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d97432, d98265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97432, d98265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97433 q = 1) (hb : d98266 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d97433, d98266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97433, d98266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97434 q = 1) (hb : d98267 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d97434, d98267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97434, d98267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97435 q = 1) (hb : d98268 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d97435, d98268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97435, d98268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97436 q = 1) (hb : d98269 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d97436, d98269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97436, d98269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12907 (p : Pattern) (ha : d97442 p = 1) (hb : d98275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97437 q = 1) (hb : d98270 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d97437, d98270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12906 q ha hb
    | true =>
      simp only [d97437, d98270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97438 q = 1) (hb : d98271 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d97438, d98271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97438, d98271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97439 q = 1) (hb : d98272 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d97439, d98272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97439, d98272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97440 q = 1) (hb : d98273 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d97440, d98273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97440, d98273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97441 q = 1) (hb : d98274 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d97441, d98274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97441, d98274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97442 q = 1) (hb : d98275 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d97442, d98275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97442, d98275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12908 (p : Pattern) (ha : d97448 p = 1) (hb : d98281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97443 q = 1) (hb : d98276 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d97443, d98276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12907 q ha hb
    | true =>
      simp only [d97443, d98276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97444 q = 1) (hb : d98277 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d97444, d98277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97444, d98277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97445 q = 1) (hb : d98278 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d97445, d98278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97445, d98278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97446 q = 1) (hb : d98279 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d97446, d98279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97446, d98279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97447 q = 1) (hb : d98280 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d97447, d98280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97447, d98280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97448 q = 1) (hb : d98281 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d97448, d98281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97448, d98281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12909 (p : Pattern) (ha : d97454 p = 1) (hb : d98287 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97449 q = 1) (hb : d98282 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d97449, d98282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12908 q ha hb
    | true =>
      simp only [d97449, d98282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97450 q = 1) (hb : d98283 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d97450, d98283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97450, d98283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97451 q = 1) (hb : d98284 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d97451, d98284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97451, d98284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97452 q = 1) (hb : d98285 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d97452, d98285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97452, d98285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97453 q = 1) (hb : d98286 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d97453, d98286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97453, d98286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97454 q = 1) (hb : d98287 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d97454, d98287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97454, d98287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12910 (p : Pattern) (ha : d53647 p = 1) (hb : d94755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12398 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12399 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12418 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12419 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
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
theorem andIntro12911 (p : Pattern) (ha : d53655 p = 1) (hb : d94755 p = 1) : d98290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d94755 q = 1) : d97471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12402 q ha hb
    | true =>
      simp only [d204, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12391 q ha hb
  have h2 (q : Pattern) (ha : d287 q = 1) (hb : d94755 q = 1) : d97520 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d288 q = 1) (hb : d94755 q = 1) : d97521 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d288, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d289 q = 1) (hb : d94755 q = 1) : d97522 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d290 q = 1) (hb : d94755 q = 1) : d97523 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53655 q = 1) (hb : d94755 q = 1) : d98290 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, d98290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, d98290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12912 (p : Pattern) (ha : d53665 p = 1) (hb : d94755 p = 1) : d98300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d94755 q = 1) : d97496 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12405 q ha hb
    | true =>
      simp only [d244, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12395 q ha hb
  have h2 (q : Pattern) (ha : d53661 q = 1) (hb : d94755 q = 1) : d98296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d98296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53661, d98296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53662 q = 1) (hb : d94755 q = 1) : d98297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d98297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53662, d98297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53663 q = 1) (hb : d94755 q = 1) : d98298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, d98298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, d98298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53664 q = 1) (hb : d94755 q = 1) : d98299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, d98299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, d98299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53665 q = 1) (hb : d94755 q = 1) : d98300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, d98300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, d98300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12913 (p : Pattern) (ha : d53671 p = 1) (hb : d94755 p = 1) : d98306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d94755 q = 1) : d97525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12415 q ha hb
    | true =>
      simp only [d292, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12416 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d94755 q = 1) : d97526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d94755 q = 1) : d98288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, d98288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, d98288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d94755 q = 1) : d98289 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, d98289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, d98289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d94755 q = 1) : d98291 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, d98291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, d98291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12911 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d94755 q = 1) : d98292 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, d98292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, d98292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d94755 q = 1) : d98293 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, d98293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, d98293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d94755 q = 1) : d98294 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, d98294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, d98294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d94755 q = 1) : d98295 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, d98295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, d98295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d94755 q = 1) : d98301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, d98301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, d98301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12912 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d94755 q = 1) : d98302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, d98302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, d98302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d94755 q = 1) : d98303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, d98303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, d98303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d94755 q = 1) : d98304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, d98304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, d98304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d94755 q = 1) : d98305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, d98305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, d98305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d94755 q = 1) : d98306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, d98306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, d98306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12914 (p : Pattern) (ha : d53677 p = 1) (hb : d94755 p = 1) : d98312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12910 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d94755 q = 1) : d98307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, d98307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, d98307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12913 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d94755 q = 1) : d98308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, d98308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, d98308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d94755 q = 1) : d98309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, d98309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, d98309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d94755 q = 1) : d98310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, d98310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, d98310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d94755 q = 1) : d98311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, d98311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, d98311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d94755 q = 1) : d98312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, d98312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, d98312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12915 (p : Pattern) (ha : d53680 p = 1) (hb : d94755 p = 1) : d98315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d502 q = 1) (hb : d94755 q = 1) : d97629 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12447 q ha hb
    | true =>
      simp only [d502, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12448 q ha hb
  have h2 (q : Pattern) (ha : d503 q = 1) (hb : d94755 q = 1) : d97630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d504 q = 1) (hb : d94755 q = 1) : d97631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d504, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d505 q = 1) (hb : d94755 q = 1) : d97632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d506 q = 1) (hb : d94755 q = 1) : d97633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53680 q = 1) (hb : d94755 q = 1) : d98315 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, d98315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, d98315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12916 (p : Pattern) (ha : d689 p = 1) (hb : d94755 p = 1) : d97713 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d676 q = 1) (hb : d94755 q = 1) : d97708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d676, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12477 q ha hb
    | true =>
      simp only [d676, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d677 q = 1) (hb : d94755 q = 1) : d97709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d677, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d677, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12452 q ha hb
    | true =>
      simp only [d684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d686 q = 1) (hb : d94755 q = 1) : d97710 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d686, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d686, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d687 q = 1) (hb : d94755 q = 1) : d97711 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d687, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d687, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d688 q = 1) (hb : d94755 q = 1) : d97712 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d688, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d688, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d689 q = 1) (hb : d94755 q = 1) : d97713 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d689, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d689, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12917 (p : Pattern) (ha : d53691 p = 1) (hb : d94755 p = 1) : d98325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53686 q = 1) (hb : d94755 q = 1) : d97716 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53686, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12916 q ha hb
    | true =>
      simp only [d53686, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12453 q ha hb
  have h2 (q : Pattern) (ha : d53687 q = 1) (hb : d94755 q = 1) : d98321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d98321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53687, d98321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53688 q = 1) (hb : d94755 q = 1) : d98322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d98322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53688, d98322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53689 q = 1) (hb : d94755 q = 1) : d98323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, d98323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, d98323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53690 q = 1) (hb : d94755 q = 1) : d98324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, d98324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, d98324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53691 q = 1) (hb : d94755 q = 1) : d98325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, d98325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, d98325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12918 (p : Pattern) (ha : d53697 p = 1) (hb : d94755 p = 1) : d98331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d94755 q = 1) : d97635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12446 q ha hb
    | true =>
      simp only [d508, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12449 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d94755 q = 1) : d97636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d94755 q = 1) : d98313 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, d98313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, d98313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d94755 q = 1) : d98314 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, d98314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, d98314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d94755 q = 1) : d98316 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, d98316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, d98316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12915 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d94755 q = 1) : d98317 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, d98317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, d98317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d94755 q = 1) : d98318 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, d98318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, d98318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d94755 q = 1) : d98319 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, d98319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, d98319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d94755 q = 1) : d98320 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, d98320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, d98320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d94755 q = 1) : d98326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, d98326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, d98326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12917 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d94755 q = 1) : d98327 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, d98327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, d98327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d94755 q = 1) : d98328 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, d98328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, d98328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d94755 q = 1) : d98329 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, d98329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, d98329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d94755 q = 1) : d98330 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, d98330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, d98330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d94755 q = 1) : d98331 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, d98331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, d98331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12919 (p : Pattern) (ha : d53703 p = 1) (hb : d94755 p = 1) : d98337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d94755 q = 1) : d98332 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, d98332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, d98332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12918 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d94755 q = 1) : d98333 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, d98333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, d98333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d94755 q = 1) : d98334 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, d98334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, d98334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d94755 q = 1) : d98335 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, d98335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, d98335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d94755 q = 1) : d98336 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, d98336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, d98336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d94755 q = 1) : d98337 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, d98337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, d98337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12920 (p : Pattern) (ha : d53707 p = 1) (hb : d94755 p = 1) : d98341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d794 q = 1) (hb : d94755 q = 1) : d97753 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12494 q ha hb
    | true =>
      simp only [d794, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12495 q ha hb
  have h2 (q : Pattern) (ha : d795 q = 1) (hb : d94755 q = 1) : d97754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d796 q = 1) (hb : d94755 q = 1) : d97755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d796, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d797 q = 1) (hb : d94755 q = 1) : d97756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d798 q = 1) (hb : d94755 q = 1) : d97757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53707 q = 1) (hb : d94755 q = 1) : d98341 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, d98341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, d98341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12921 (p : Pattern) (ha : d1011 p = 1) (hb : d94755 p = 1) : d97838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d94755 q = 1) : d97833 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12525 q ha hb
    | true =>
      simp only [d998, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d94755 q = 1) : d97834 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12499 q ha hb
    | true =>
      simp only [d1006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1008 q = 1) (hb : d94755 q = 1) : d97835 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1008, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1008, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1009 q = 1) (hb : d94755 q = 1) : d97836 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1009, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1009, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1010 q = 1) (hb : d94755 q = 1) : d97837 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1010, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1010, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1011 q = 1) (hb : d94755 q = 1) : d97838 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1011, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1011, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12922 (p : Pattern) (ha : d53718 p = 1) (hb : d94755 p = 1) : d98351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53713 q = 1) (hb : d94755 q = 1) : d97841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53713, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12921 q ha hb
    | true =>
      simp only [d53713, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12500 q ha hb
  have h2 (q : Pattern) (ha : d53714 q = 1) (hb : d94755 q = 1) : d98347 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d98347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53714, d98347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53715 q = 1) (hb : d94755 q = 1) : d98348 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d98348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53715, d98348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53716 q = 1) (hb : d94755 q = 1) : d98349 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, d98349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, d98349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53717 q = 1) (hb : d94755 q = 1) : d98350 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, d98350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, d98350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53718 q = 1) (hb : d94755 q = 1) : d98351 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, d98351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, d98351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12923 (p : Pattern) (ha : d53724 p = 1) (hb : d94755 p = 1) : d98357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d94755 q = 1) : d97759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12493 q ha hb
    | true =>
      simp only [d800, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12496 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d94755 q = 1) : d97760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d94755 q = 1) : d98339 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, d98339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, d98339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d94755 q = 1) : d98340 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, d98340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, d98340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d94755 q = 1) : d98342 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, d98342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, d98342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12920 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d94755 q = 1) : d98343 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, d98343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, d98343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d94755 q = 1) : d98344 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, d98344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, d98344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d94755 q = 1) : d98345 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, d98345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, d98345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d94755 q = 1) : d98346 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, d98346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, d98346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d94755 q = 1) : d98352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, d98352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, d98352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12922 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d94755 q = 1) : d98353 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, d98353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, d98353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d94755 q = 1) : d98354 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, d98354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, d98354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d94755 q = 1) : d98355 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, d98355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, d98355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d94755 q = 1) : d98356 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, d98356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, d98356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d94755 q = 1) : d98357 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, d98357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, d98357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12924 (p : Pattern) (ha : d53730 p = 1) (hb : d94755 p = 1) : d98363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d94755 q = 1) : d98358 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, d98358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, d98358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12923 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d94755 q = 1) : d98359 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, d98359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, d98359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d94755 q = 1) : d98360 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, d98360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, d98360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d94755 q = 1) : d98361 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, d98361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, d98361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d94755 q = 1) : d98362 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, d98362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, d98362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d94755 q = 1) : d98363 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, d98363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, d98363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12925 (p : Pattern) (ha : d53735 p = 1) (hb : d94755 p = 1) : d98368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1173 q = 1) (hb : d94755 q = 1) : d97879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12543 q ha hb
    | true =>
      simp only [d1173, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12544 q ha hb
  have h2 (q : Pattern) (ha : d1174 q = 1) (hb : d94755 q = 1) : d97880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1175 q = 1) (hb : d94755 q = 1) : d97881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1175, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1176 q = 1) (hb : d94755 q = 1) : d97882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1177 q = 1) (hb : d94755 q = 1) : d97883 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53735 q = 1) (hb : d94755 q = 1) : d98368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, d98368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, d98368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12926 (p : Pattern) (ha : d1436 p = 1) (hb : d94755 p = 1) : d97964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d94755 q = 1) : d97959 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12575 q ha hb
    | true =>
      simp only [d1423, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d94755 q = 1) : d97960 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12548 q ha hb
    | true =>
      simp only [d1431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1433 q = 1) (hb : d94755 q = 1) : d97961 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1433, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1434 q = 1) (hb : d94755 q = 1) : d97962 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1434, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1435 q = 1) (hb : d94755 q = 1) : d97963 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1435, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1436 q = 1) (hb : d94755 q = 1) : d97964 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1436, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12927 (p : Pattern) (ha : d53746 p = 1) (hb : d94755 p = 1) : d98378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53741 q = 1) (hb : d94755 q = 1) : d97967 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53741, d97967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12926 q ha hb
    | true =>
      simp only [d53741, d97967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12549 q ha hb
  have h2 (q : Pattern) (ha : d53742 q = 1) (hb : d94755 q = 1) : d98374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d98374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53742, d98374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53743 q = 1) (hb : d94755 q = 1) : d98375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d98375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53743, d98375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53744 q = 1) (hb : d94755 q = 1) : d98376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, d98376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, d98376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53745 q = 1) (hb : d94755 q = 1) : d98377 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, d98377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, d98377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53746 q = 1) (hb : d94755 q = 1) : d98378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, d98378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, d98378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12928 (p : Pattern) (ha : d53752 p = 1) (hb : d94755 p = 1) : d98384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d94755 q = 1) : d97885 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d97885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12542 q ha hb
    | true =>
      simp only [d1179, d97885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12545 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d94755 q = 1) : d97886 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d97886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, d97886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d94755 q = 1) : d98366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, d98366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, d98366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d94755 q = 1) : d98367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, d98367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, d98367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d94755 q = 1) : d98369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, d98369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, d98369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12925 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d94755 q = 1) : d98370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, d98370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, d98370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d94755 q = 1) : d98371 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, d98371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, d98371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d94755 q = 1) : d98372 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, d98372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, d98372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d94755 q = 1) : d98373 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, d98373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, d98373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d94755 q = 1) : d98379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, d98379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, d98379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12927 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d94755 q = 1) : d98380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, d98380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, d98380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d94755 q = 1) : d98381 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, d98381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, d98381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d94755 q = 1) : d98382 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, d98382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, d98382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d94755 q = 1) : d98383 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, d98383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, d98383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d94755 q = 1) : d98384 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, d98384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, d98384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12929 (p : Pattern) (ha : d53758 p = 1) (hb : d94755 p = 1) : d98390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d94755 q = 1) : d98385 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, d98385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, d98385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12928 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d94755 q = 1) : d98386 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, d98386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, d98386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d94755 q = 1) : d98387 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, d98387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, d98387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d94755 q = 1) : d98388 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, d98388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, d98388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d94755 q = 1) : d98389 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, d98389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, d98389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d94755 q = 1) : d98390 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, d98390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, d98390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12930 (p : Pattern) (ha : d53764 p = 1) (hb : d94755 p = 1) : d98396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1634 q = 1) (hb : d94755 q = 1) : d98006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12593 q ha hb
    | true =>
      simp only [d1634, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12594 q ha hb
  have h2 (q : Pattern) (ha : d1635 q = 1) (hb : d94755 q = 1) : d98007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1636 q = 1) (hb : d94755 q = 1) : d98008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1636, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1637 q = 1) (hb : d94755 q = 1) : d98009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1638 q = 1) (hb : d94755 q = 1) : d98010 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53764 q = 1) (hb : d94755 q = 1) : d98396 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, d98396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, d98396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12931 (p : Pattern) (ha : d1913 p = 1) (hb : d94755 p = 1) : d98091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d94755 q = 1) : d98086 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12625 q ha hb
    | true =>
      simp only [d1900, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d94755 q = 1) : d98087 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12598 q ha hb
    | true =>
      simp only [d1908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1910 q = 1) (hb : d94755 q = 1) : d98088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1910, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1911 q = 1) (hb : d94755 q = 1) : d98089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1911, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1912 q = 1) (hb : d94755 q = 1) : d98090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1912, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1913 q = 1) (hb : d94755 q = 1) : d98091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1913, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12932 (p : Pattern) (ha : d53775 p = 1) (hb : d94755 p = 1) : d98406 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53770 q = 1) (hb : d94755 q = 1) : d98094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53770, d98094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12931 q ha hb
    | true =>
      simp only [d53770, d98094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12599 q ha hb
  have h2 (q : Pattern) (ha : d53771 q = 1) (hb : d94755 q = 1) : d98402 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d98402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53771, d98402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53772 q = 1) (hb : d94755 q = 1) : d98403 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d98403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53772, d98403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53773 q = 1) (hb : d94755 q = 1) : d98404 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, d98404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, d98404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53774 q = 1) (hb : d94755 q = 1) : d98405 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, d98405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, d98405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53775 q = 1) (hb : d94755 q = 1) : d98406 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, d98406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, d98406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12933 (p : Pattern) (ha : d53781 p = 1) (hb : d94755 p = 1) : d98412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d94755 q = 1) : d98012 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d98012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12592 q ha hb
    | true =>
      simp only [d1640, d98012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12595 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d94755 q = 1) : d98013 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d98013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, d98013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d94755 q = 1) : d98394 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, d98394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, d98394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d94755 q = 1) : d98395 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, d98395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, d98395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d94755 q = 1) : d98397 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, d98397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, d98397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12930 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d94755 q = 1) : d98398 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, d98398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, d98398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d94755 q = 1) : d98399 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, d98399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, d98399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d94755 q = 1) : d98400 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, d98400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, d98400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d94755 q = 1) : d98401 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, d98401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, d98401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d94755 q = 1) : d98407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, d98407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, d98407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12932 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d94755 q = 1) : d98408 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, d98408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, d98408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d94755 q = 1) : d98409 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, d98409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, d98409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d94755 q = 1) : d98410 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, d98410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, d98410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d94755 q = 1) : d98411 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, d98411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, d98411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d94755 q = 1) : d98412 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, d98412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, d98412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12934 (p : Pattern) (ha : d53787 p = 1) (hb : d94755 p = 1) : d98418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d94755 q = 1) : d98413 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, d98413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, d98413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12933 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d94755 q = 1) : d98414 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, d98414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, d98414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d94755 q = 1) : d98415 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, d98415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, d98415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d94755 q = 1) : d98416 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, d98416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, d98416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d94755 q = 1) : d98417 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, d98417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, d98417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d94755 q = 1) : d98418 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, d98418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, d98418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12935 (p : Pattern) (ha : d53794 p = 1) (hb : d94755 p = 1) : d98425 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2117 q = 1) (hb : d94755 q = 1) : d98134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12643 q ha hb
    | true =>
      simp only [d2117, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12644 q ha hb
  have h2 (q : Pattern) (ha : d2118 q = 1) (hb : d94755 q = 1) : d98135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2119 q = 1) (hb : d94755 q = 1) : d98136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2119, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2120 q = 1) (hb : d94755 q = 1) : d98137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2121 q = 1) (hb : d94755 q = 1) : d98138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53794 q = 1) (hb : d94755 q = 1) : d98425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, d98425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, d98425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12936 (p : Pattern) (ha : d2391 p = 1) (hb : d94755 p = 1) : d98219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d94755 q = 1) : d98214 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12675 q ha hb
    | true =>
      simp only [d2378, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d94755 q = 1) : d98215 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12648 q ha hb
    | true =>
      simp only [d2386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2388 q = 1) (hb : d94755 q = 1) : d98216 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2388, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2388, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2389 q = 1) (hb : d94755 q = 1) : d98217 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2389, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2389, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2390 q = 1) (hb : d94755 q = 1) : d98218 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2390, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2390, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2391 q = 1) (hb : d94755 q = 1) : d98219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2391, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2391, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro12937 (p : Pattern) (ha : d53805 p = 1) (hb : d94755 p = 1) : d98435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53800 q = 1) (hb : d94755 q = 1) : d98222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d53800, d98222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12936 q ha hb
    | true =>
      simp only [d53800, d98222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12649 q ha hb
  have h2 (q : Pattern) (ha : d53801 q = 1) (hb : d94755 q = 1) : d98431 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d98431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53801, d98431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53802 q = 1) (hb : d94755 q = 1) : d98432 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d98432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53802, d98432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53803 q = 1) (hb : d94755 q = 1) : d98433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, d98433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, d98433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53804 q = 1) (hb : d94755 q = 1) : d98434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, d98434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, d98434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53805 q = 1) (hb : d94755 q = 1) : d98435 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, d98435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, d98435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12938 (p : Pattern) (ha : d53811 p = 1) (hb : d94755 p = 1) : d98441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d94755 q = 1) : d98140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d98140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12642 q ha hb
    | true =>
      simp only [d2123, d98140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12645 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d94755 q = 1) : d98141 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d98141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, d98141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d94755 q = 1) : d98423 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, d98423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, d98423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d94755 q = 1) : d98424 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, d98424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, d98424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d94755 q = 1) : d98426 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, d98426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, d98426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12935 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d94755 q = 1) : d98427 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, d98427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, d98427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d94755 q = 1) : d98428 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, d98428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, d98428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d94755 q = 1) : d98429 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, d98429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, d98429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d94755 q = 1) : d98430 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, d98430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, d98430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d94755 q = 1) : d98436 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, d98436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, d98436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12937 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d94755 q = 1) : d98437 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, d98437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, d98437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d94755 q = 1) : d98438 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, d98438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, d98438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d94755 q = 1) : d98439 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, d98439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, d98439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d94755 q = 1) : d98440 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, d98440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, d98440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d94755 q = 1) : d98441 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, d98441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, d98441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro12939 (p : Pattern) (ha : d53817 p = 1) (hb : d94755 p = 1) : d98447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d94755 q = 1) : d98442 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, d98442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, d98442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12938 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d94755 q = 1) : d98443 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, d98443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, d98443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d94755 q = 1) : d98444 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, d98444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, d98444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d94755 q = 1) : d98445 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, d98445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, d98445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d94755 q = 1) : d98446 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, d98446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, d98446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d94755 q = 1) : d98447 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, d98447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, d98447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12940 (p : Pattern) (ha : d53823 p = 1) (hb : d94755 p = 1) : d98453 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d94755 q = 1) : d98338 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, d98338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12914 q ha hb
    | true =>
      simp only [d53704, d98338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12919 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d94755 q = 1) : d98364 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, d98364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, d98364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12924 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d94755 q = 1) : d98365 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, d98365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, d98365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d94755 q = 1) : d98391 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, d98391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, d98391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12929 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d94755 q = 1) : d98392 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, d98392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, d98392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d94755 q = 1) : d98393 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, d98393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, d98393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d94755 q = 1) : d98419 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, d98419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, d98419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12934 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d94755 q = 1) : d98420 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, d98420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, d98420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d94755 q = 1) : d98421 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, d98421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, d98421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d94755 q = 1) : d98422 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, d98422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, d98422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d94755 q = 1) : d98448 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, d98448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, d98448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12939 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d94755 q = 1) : d98449 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, d98449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, d98449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d94755 q = 1) : d98450 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, d98450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, d98450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d94755 q = 1) : d98451 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, d98451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, d98451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d94755 q = 1) : d98452 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, d98452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, d98452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d94755 q = 1) : d98453 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, d98453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, d98453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro12941 (p : Pattern) (ha : d53829 p = 1) (hb : d94755 p = 1) : d98459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d94755 q = 1) : d98454 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, d98454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12940 q ha hb
    | true =>
      simp only [d53824, d98454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d94755 q = 1) : d98455 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, d98455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, d98455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d94755 q = 1) : d98456 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, d98456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, d98456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d94755 q = 1) : d98457 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, d98457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, d98457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d94755 q = 1) : d98458 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, d98458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, d98458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d94755 q = 1) : d98459 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, d98459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, d98459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12942 (p : Pattern) (ha : d53835 p = 1) (hb : d94755 p = 1) : d98465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d94755 q = 1) : d98460 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, d98460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12941 q ha hb
    | true =>
      simp only [d53830, d98460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d94755 q = 1) : d98461 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, d98461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, d98461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d94755 q = 1) : d98462 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, d98462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, d98462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d94755 q = 1) : d98463 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, d98463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, d98463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d94755 q = 1) : d98464 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, d98464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, d98464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d94755 q = 1) : d98465 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, d98465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, d98465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12943 (p : Pattern) (ha : d53841 p = 1) (hb : d94755 p = 1) : d98471 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d94755 q = 1) : d98466 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, d98466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12942 q ha hb
    | true =>
      simp only [d53836, d98466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d94755 q = 1) : d98467 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, d98467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, d98467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d94755 q = 1) : d98468 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, d98468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, d98468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d94755 q = 1) : d98469 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, d98469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, d98469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d94755 q = 1) : d98470 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, d98470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, d98470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d94755 q = 1) : d98471 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, d98471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, d98471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12944 (p : Pattern) (ha : d53847 p = 1) (hb : d94755 p = 1) : d98477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d94755 q = 1) : d98472 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, d98472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12943 q ha hb
    | true =>
      simp only [d53842, d98472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d94755 q = 1) : d98473 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, d98473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, d98473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d94755 q = 1) : d98474 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, d98474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, d98474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d94755 q = 1) : d98475 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, d98475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, d98475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d94755 q = 1) : d98476 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, d98476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, d98476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d94755 q = 1) : d98477 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, d98477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, d98477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12945 (p : Pattern) (ha : d53853 p = 1) (hb : d94756 p = 1) : d98483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94755 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d94755 q = 1) : d98478 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, d98478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12944 q ha hb
    | true =>
      simp only [d53848, d98478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d94755 q = 1) : d98479 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, d98479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, d98479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53850 q = 1) (hb : d94756 q = 1) : d98480 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, d94756, d98480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, d94756, d98480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53851 q = 1) (hb : d94756 q = 1) : d98481 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d98481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53851, d98481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53852 q = 1) (hb : d94756 q = 1) : d98482 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, d98482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53852, d98482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d53853 q = 1) (hb : d94756 q = 1) : d98483 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, d98483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53853, d98483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro12946 (p : Pattern) (ha : d53859 p = 1) (hb : d94756 p = 1) : d98489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d94756 q = 1) : d98484 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, d98484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12945 q ha hb
    | true =>
      simp only [d53854, d98484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d94756 q = 1) : d98485 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, d98485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, d98485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53856 q = 1) (hb : d94756 q = 1) : d98486 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d98486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d98486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53857 q = 1) (hb : d94756 q = 1) : d98487 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, d98487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53857, d98487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53858 q = 1) (hb : d94756 q = 1) : d98488 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, d98488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53858, d98488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53859 q = 1) (hb : d94756 q = 1) : d98489 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, d98489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53859, d98489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12947 (p : Pattern) (ha : d53865 p = 1) (hb : d94756 p = 1) : d98495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94756 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d94756 q = 1) : d98490 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, d98490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12946 q ha hb
    | true =>
      simp only [d53860, d98490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d94756 q = 1) : d98491 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, d98491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, d98491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d94756 q = 1) : d98492 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, d98492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, d98492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d94756 q = 1) : d98493 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, d98493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, d98493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d94756 q = 1) : d98494 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, d98494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, d98494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d94756 q = 1) : d98495 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, d98495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, d98495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro12948 (p : Pattern) (ha : d96325 p = 1) (hb : d97517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96302 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96320 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d96321 q = 1) (hb : d97513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96321, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d96321, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96232 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96322 q = 1) (hb : d97514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96322, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96322, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96323 q = 1) (hb : d97515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96323, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96323, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96324 q = 1) (hb : d97516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96324, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96324, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96325 q = 1) (hb : d97517 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96325, d97517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96325, d97517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12949 (p : Pattern) (ha : d96341 p = 1) (hb : d97524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96302 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96231 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12696 q ha hb
    | true =>
      simp only [d96231, d97464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96321 q = 1) (hb : d97513 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96321, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96321, d97513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96232 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96322 q = 1) (hb : d97514 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96322, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96322, d97514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96323 q = 1) (hb : d97515 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96323, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96323, d97515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96324 q = 1) (hb : d97516 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96324, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96324, d97516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d96330 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96334 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d96336 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d96238 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
    | true =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d96337 q = 1) (hb : d97520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96337, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d96337, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d96239 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d96338 q = 1) (hb : d97521 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96338, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d96338, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d96339 q = 1) (hb : d97522 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96339, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d96339, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d96340 q = 1) (hb : d97523 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96340, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d96340, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d96341 q = 1) (hb : d97524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96341, d97524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96341, d97524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro12950 (p : Pattern) (ha : d96350 p = 1) (hb : d98290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96336 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96238 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12698 q ha hb
    | true =>
      simp only [d96238, d97471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96337 q = 1) (hb : d97520 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96337, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96337, d97520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96239 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96338 q = 1) (hb : d97521 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96338, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96338, d97521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96348 q = 1) (hb : d97522 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96348, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96348, d97522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96349 q = 1) (hb : d97523 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96349, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96349, d97523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96350 q = 1) (hb : d98290 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96350, d98290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96350, d98290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12951 (p : Pattern) (ha : d96372 p = 1) (hb : d98300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96367 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96265 q = 1) (hb : d97496 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96265, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12703 q ha hb
    | true =>
      simp only [d96265, d97496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d96368 q = 1) (hb : d98296 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96368, d98296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96368, d98296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96266 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96369 q = 1) (hb : d98297 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96369, d98297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96369, d98297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96370 q = 1) (hb : d98298 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96370, d98298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96370, d98298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96371 q = 1) (hb : d98299 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96371, d98299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96371, d98299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96372 q = 1) (hb : d98300 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96372, d98300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96372, d98300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro12952 (p : Pattern) (ha : d96378 p = 1) (hb : d98306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96296 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96342 q = 1) (hb : d97525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96342, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12948 q ha hb
    | true =>
      simp only [d96342, d97525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12949 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96345 q = 1) (hb : d97526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96345, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96345, d97526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96346 q = 1) (hb : d98288 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96346, d98288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96346, d98288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96347 q = 1) (hb : d98289 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96347, d98289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96347, d98289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96351 q = 1) (hb : d98291 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96351, d98291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96351, d98291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12950 q ha hb
  have h8 (q : Pattern) (ha : d96352 q = 1) (hb : d98292 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96352, d98292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96352, d98292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d96353 q = 1) (hb : d98293 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96353, d98293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d96353, d98293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d96354 q = 1) (hb : d98294 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96354, d98294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96354, d98294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d96355 q = 1) (hb : d98295 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96355, d98295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96355, d98295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d96373 q = 1) (hb : d98301 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96373, d98301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96373, d98301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12951 q ha hb
  have h13 (q : Pattern) (ha : d96374 q = 1) (hb : d98302 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96374, d98302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96374, d98302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d96375 q = 1) (hb : d98303 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96375, d98303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96375, d98303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d96376 q = 1) (hb : d98304 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96376, d98304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d96376, d98304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d96377 q = 1) (hb : d98305 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96377, d98305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96377, d98305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d96378 q = 1) (hb : d98306 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96378, d98306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d96378, d98306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro12953 (p : Pattern) (ha : d96384 p = 1) (hb : d98312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96281 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96379 q = 1) (hb : d98307 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96379, d98307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96379, d98307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12952 q ha hb
  have h3 (q : Pattern) (ha : d96380 q = 1) (hb : d98308 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96380, d98308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96380, d98308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96381 q = 1) (hb : d98309 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96381, d98309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96381, d98309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96382 q = 1) (hb : d98310 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96382, d98310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96382, d98310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96383 q = 1) (hb : d98311 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96383, d98311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96383, d98311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96384 q = 1) (hb : d98312 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96384, d98312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96384, d98312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro12954 (p : Pattern) (ha : d96442 p = 1) (hb : d97625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96405 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96431 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96230 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96320 q = 1) (hb : d97620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96320, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12727 q ha hb
    | true =>
      simp only [d96320, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96432 q = 1) (hb : d97621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96432, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d96432, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96438 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96439 q = 1) (hb : d97622 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96439, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96439, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96440 q = 1) (hb : d97623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96440, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96440, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96441 q = 1) (hb : d97624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96441, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96441, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96442 q = 1) (hb : d97625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96442, d97625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96442, d97625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12955 (p : Pattern) (ha : d96462 p = 1) (hb : d97634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96405 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96411 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96431 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96230 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96320 q = 1) (hb : d97620 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96320, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12727 q ha hb
    | true =>
      simp only [d96320, d97620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96432 q = 1) (hb : d97621 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96432, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96432, d97621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96438 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96439 q = 1) (hb : d97622 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96439, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96439, d97622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96440 q = 1) (hb : d97623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96440, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96440, d97623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96441 q = 1) (hb : d97624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96441, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96441, d97624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d96447 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96451 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d96454 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d96237 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d96336 q = 1) (hb : d97629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96336, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12729 q ha hb
    | true =>
      simp only [d96336, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d96455 q = 1) (hb : d97630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96455, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d96455, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d96458 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d96459 q = 1) (hb : d97631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96459, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96459, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d96460 q = 1) (hb : d97632 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96460, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d96460, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d96461 q = 1) (hb : d97633 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96461, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d96461, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d96462 q = 1) (hb : d97634 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96462, d97634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96462, d97634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro12956 (p : Pattern) (ha : d96476 p = 1) (hb : d98315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96454 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96237 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96336 q = 1) (hb : d97629 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96336, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12729 q ha hb
    | true =>
      simp only [d96336, d97629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96455 q = 1) (hb : d97630 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96455, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96455, d97630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d96458 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d96459 q = 1) (hb : d97631 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96459, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96459, d97631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d96474 q = 1) (hb : d97632 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96474, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96474, d97632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96475 q = 1) (hb : d97633 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96475, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96475, d97633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96476 q = 1) (hb : d98315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96476, d98315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96476, d98315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12957 (p : Pattern) (ha : d96366 p = 1) (hb : d97713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96361 q = 1) (hb : d97708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96361, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12753 q ha hb
    | true =>
      simp only [d96361, d97708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96362 q = 1) (hb : d97709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96362, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96362, d97709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96260 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96363 q = 1) (hb : d97710 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96363, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96363, d97710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96364 q = 1) (hb : d97711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96364, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96364, d97711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96365 q = 1) (hb : d97712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96365, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96365, d97712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96366 q = 1) (hb : d97713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96366, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96366, d97713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12958 (p : Pattern) (ha : d96514 p = 1) (hb : d98325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96367 q = 1) (hb : d97716 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96367, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12957 q ha hb
    | true =>
      simp only [d96367, d97716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96504 q = 1) (hb : d98321 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96504, d98321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96504, d98321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d96510 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d96511 q = 1) (hb : d98322 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96511, d98322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96511, d98322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d96512 q = 1) (hb : d98323 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96512, d98323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96512, d98323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96513 q = 1) (hb : d98324 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96513, d98324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96513, d98324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96514 q = 1) (hb : d98325 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96514, d98325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96514, d98325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12959 (p : Pattern) (ha : d96526 p = 1) (hb : d98331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96399 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96463 q = 1) (hb : d97635 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96463, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12954 q ha hb
    | true =>
      simp only [d96463, d97635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12955 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96470 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96471 q = 1) (hb : d97636 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96471, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96471, d97636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96472 q = 1) (hb : d98313 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96472, d98313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96472, d98313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96473 q = 1) (hb : d98314 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96473, d98314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96473, d98314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96477 q = 1) (hb : d98316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96477, d98316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96477, d98316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12956 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d96479 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d96480 q = 1) (hb : d98317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96480, d98317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96480, d98317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d96481 q = 1) (hb : d98318 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96481, d98318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96481, d98318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d96482 q = 1) (hb : d98319 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96482, d98319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96482, d98319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d96483 q = 1) (hb : d98320 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96483, d98320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96483, d98320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d96515 q = 1) (hb : d98326 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96515, d98326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96515, d98326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12958 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d96521 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d96522 q = 1) (hb : d98327 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96522, d98327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96522, d98327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d96523 q = 1) (hb : d98328 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96523, d98328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96523, d98328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d96524 q = 1) (hb : d98329 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96524, d98329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d96524, d98329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d96525 q = 1) (hb : d98330 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96525, d98330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96525, d98330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d96526 q = 1) (hb : d98331 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96526, d98331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96526, d98331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro12960 (p : Pattern) (ha : d96532 p = 1) (hb : d98337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96527 q = 1) (hb : d98332 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96527, d98332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96527, d98332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12959 q ha hb
  have h2 (q : Pattern) (ha : d96528 q = 1) (hb : d98333 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96528, d98333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96528, d98333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96529 q = 1) (hb : d98334 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96529, d98334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96529, d98334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96530 q = 1) (hb : d98335 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96530, d98335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96530, d98335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96531 q = 1) (hb : d98336 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96531, d98336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96531, d98336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96532 q = 1) (hb : d98337 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96532, d98337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96532, d98337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12961 (p : Pattern) (ha : d96622 p = 1) (hb : d97749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96582 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96611 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96555 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96556 q = 1) (hb : d97744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96556, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12761 q ha hb
    | true =>
      simp only [d96556, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96612 q = 1) (hb : d97745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96612, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d96612, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96618 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96619 q = 1) (hb : d97746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96619, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96619, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96620 q = 1) (hb : d97747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96620, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96620, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96621 q = 1) (hb : d97748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96621, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96621, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96622 q = 1) (hb : d97749 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96622, d97749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96622, d97749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12962 (p : Pattern) (ha : d96644 p = 1) (hb : d97758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96591 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96555 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96556 q = 1) (hb : d97744 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96556, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12761 q ha hb
    | true =>
      simp only [d96556, d97744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96612 q = 1) (hb : d97745 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96612, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96612, d97745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96618 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96619 q = 1) (hb : d97746 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96619, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96619, d97746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96620 q = 1) (hb : d97747 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96620, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96620, d97747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96621 q = 1) (hb : d97748 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96621, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96621, d97748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d96628 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96633 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d96636 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d96565 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d96566 q = 1) (hb : d97753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96566, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12763 q ha hb
    | true =>
      simp only [d96566, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d96637 q = 1) (hb : d97754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96637, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d96637, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d96640 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d96641 q = 1) (hb : d97755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96641, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96641, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d96642 q = 1) (hb : d97756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96642, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d96642, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d96643 q = 1) (hb : d97757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96643, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d96643, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d96644 q = 1) (hb : d97758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96644, d97758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96644, d97758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro12963 (p : Pattern) (ha : d96669 p = 1) (hb : d98341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96636 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96565 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96566 q = 1) (hb : d97753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96566, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12763 q ha hb
    | true =>
      simp only [d96566, d97753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96637 q = 1) (hb : d97754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96637, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96637, d97754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d96640 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d96641 q = 1) (hb : d97755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96641, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96641, d97755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d96667 q = 1) (hb : d97756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96667, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96667, d97756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96668 q = 1) (hb : d97757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96668, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96668, d97757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96669 q = 1) (hb : d98341 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96669, d98341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96669, d98341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12964 (p : Pattern) (ha : d96714 p = 1) (hb : d97838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96709 q = 1) (hb : d97833 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96709, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12789 q ha hb
    | true =>
      simp only [d96709, d97833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96710 q = 1) (hb : d97834 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96710, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96710, d97834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96701 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96711 q = 1) (hb : d97835 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96711, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96711, d97835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96712 q = 1) (hb : d97836 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96712, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96712, d97836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96713 q = 1) (hb : d97837 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96713, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96713, d97837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96714 q = 1) (hb : d97838 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96714, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96714, d97838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12965 (p : Pattern) (ha : d96730 p = 1) (hb : d98351 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96706 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96718 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96719 q = 1) (hb : d97841 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96719, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12964 q ha hb
    | true =>
      simp only [d96719, d97841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96720 q = 1) (hb : d98347 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96720, d98347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96720, d98347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d96726 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d96727 q = 1) (hb : d98348 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96727, d98348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96727, d98348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d96728 q = 1) (hb : d98349 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96728, d98349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96728, d98349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96729 q = 1) (hb : d98350 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96729, d98350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96729, d98350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96730 q = 1) (hb : d98351 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96730, d98351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96730, d98351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12966 (p : Pattern) (ha : d96743 p = 1) (hb : d98357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96574 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96645 q = 1) (hb : d97759 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96645, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12961 q ha hb
    | true =>
      simp only [d96645, d97759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12962 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96663 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96664 q = 1) (hb : d97760 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96664, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96664, d97760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96665 q = 1) (hb : d98339 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96665, d98339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96665, d98339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96666 q = 1) (hb : d98340 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96666, d98340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96666, d98340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96670 q = 1) (hb : d98342 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96670, d98342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96670, d98342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12963 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d96672 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d96673 q = 1) (hb : d98343 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96673, d98343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96673, d98343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d96674 q = 1) (hb : d98344 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96674, d98344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96674, d98344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d96675 q = 1) (hb : d98345 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96675, d98345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96675, d98345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d96676 q = 1) (hb : d98346 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96676, d98346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96676, d98346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d96731 q = 1) (hb : d98352 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96731, d98352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96731, d98352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12965 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d96738 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d96739 q = 1) (hb : d98353 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96739, d98353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96739, d98353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d96740 q = 1) (hb : d98354 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96740, d98354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96740, d98354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d96741 q = 1) (hb : d98355 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96741, d98355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d96741, d98355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d96742 q = 1) (hb : d98356 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96742, d98356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96742, d98356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d96743 q = 1) (hb : d98357 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96743, d98357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96743, d98357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro12967 (p : Pattern) (ha : d96749 p = 1) (hb : d98363 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96744 q = 1) (hb : d98358 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96744, d98358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96744, d98358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12966 q ha hb
  have h2 (q : Pattern) (ha : d96745 q = 1) (hb : d98359 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96745, d98359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96745, d98359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96746 q = 1) (hb : d98360 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96746, d98360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96746, d98360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96747 q = 1) (hb : d98361 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96747, d98361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96747, d98361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96748 q = 1) (hb : d98362 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96748, d98362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96748, d98362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96749 q = 1) (hb : d98363 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96749, d98363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96749, d98363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12968 (p : Pattern) (ha : d96840 p = 1) (hb : d97875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96800 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96829 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96773 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96774 q = 1) (hb : d97870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96774, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12797 q ha hb
    | true =>
      simp only [d96774, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96830 q = 1) (hb : d97871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96830, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d96830, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d96836 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d96837 q = 1) (hb : d97872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96837, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96837, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d96838 q = 1) (hb : d97873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96838, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96838, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d96839 q = 1) (hb : d97874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96839, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96839, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d96840 q = 1) (hb : d97875 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96840, d97875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96840, d97875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12969 (p : Pattern) (ha : d96862 p = 1) (hb : d97884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96809 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96773 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96774 q = 1) (hb : d97870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96774, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12797 q ha hb
    | true =>
      simp only [d96774, d97870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96830 q = 1) (hb : d97871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96830, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d96830, d97871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d96836 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d96837 q = 1) (hb : d97872 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96837, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96837, d97872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d96838 q = 1) (hb : d97873 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96838, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96838, d97873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96839 q = 1) (hb : d97874 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96839, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96839, d97874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d96846 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d96851 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d96854 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d96783 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d96784 q = 1) (hb : d97879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96784, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12799 q ha hb
    | true =>
      simp only [d96784, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d96855 q = 1) (hb : d97880 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96855, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d96855, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d96858 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d96859 q = 1) (hb : d97881 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96859, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96859, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d96860 q = 1) (hb : d97882 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96860, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d96860, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d96861 q = 1) (hb : d97883 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96861, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d96861, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d96862 q = 1) (hb : d97884 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96862, d97884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96862, d97884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro12970 (p : Pattern) (ha : d96887 p = 1) (hb : d98368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96854 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96784 q = 1) (hb : d97879 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96784, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12799 q ha hb
    | true =>
      simp only [d96784, d97879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96855 q = 1) (hb : d97880 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96855, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96855, d97880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d96858 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d96859 q = 1) (hb : d97881 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96859, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96859, d97881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d96885 q = 1) (hb : d97882 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96885, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96885, d97882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96886 q = 1) (hb : d97883 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96886, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96886, d97883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96887 q = 1) (hb : d98368 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96887, d98368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96887, d98368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12971 (p : Pattern) (ha : d96932 p = 1) (hb : d97964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96927 q = 1) (hb : d97959 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96927, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12825 q ha hb
    | true =>
      simp only [d96927, d97959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d96928 q = 1) (hb : d97960 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96928, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96928, d97960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96919 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96929 q = 1) (hb : d97961 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96929, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d96929, d97961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d96930 q = 1) (hb : d97962 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96930, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96930, d97962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d96931 q = 1) (hb : d97963 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96931, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d96931, d97963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d96932 q = 1) (hb : d97964 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96932, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96932, d97964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12972 (p : Pattern) (ha : d96948 p = 1) (hb : d98378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d96924 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96937 q = 1) (hb : d97967 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96937, d97967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12971 q ha hb
    | true =>
      simp only [d96937, d97967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d96938 q = 1) (hb : d98374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96938, d98374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96938, d98374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d96944 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d96945 q = 1) (hb : d98375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96945, d98375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d96945, d98375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d96946 q = 1) (hb : d98376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96946, d98376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96946, d98376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d96947 q = 1) (hb : d98377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96947, d98377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96947, d98377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d96948 q = 1) (hb : d98378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96948, d98378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96948, d98378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12973 (p : Pattern) (ha : d96961 p = 1) (hb : d98384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d96792 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96863 q = 1) (hb : d97885 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96863, d97885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12968 q ha hb
    | true =>
      simp only [d96863, d97885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12969 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d96881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d96882 q = 1) (hb : d97886 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96882, d97886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d96882, d97886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96883 q = 1) (hb : d98366 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96883, d98366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96883, d98366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d96884 q = 1) (hb : d98367 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96884, d98367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96884, d98367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d96888 q = 1) (hb : d98369 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96888, d98369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96888, d98369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12970 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d96890 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d96891 q = 1) (hb : d98370 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96891, d98370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d96891, d98370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d96892 q = 1) (hb : d98371 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96892, d98371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d96892, d98371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d96893 q = 1) (hb : d98372 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96893, d98372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d96893, d98372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d96894 q = 1) (hb : d98373 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96894, d98373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d96894, d98373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d96949 q = 1) (hb : d98379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96949, d98379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d96949, d98379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12972 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d96956 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d96957 q = 1) (hb : d98380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96957, d98380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d96957, d98380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d96958 q = 1) (hb : d98381 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96958, d98381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d96958, d98381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d96959 q = 1) (hb : d98382 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96959, d98382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d96959, d98382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d96960 q = 1) (hb : d98383 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96960, d98383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d96960, d98383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d96961 q = 1) (hb : d98384 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96961, d98384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d96961, d98384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro12974 (p : Pattern) (ha : d96967 p = 1) (hb : d98390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96962 q = 1) (hb : d98385 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96962, d98385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96962, d98385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12973 q ha hb
  have h2 (q : Pattern) (ha : d96963 q = 1) (hb : d98386 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96963, d98386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96963, d98386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d96964 q = 1) (hb : d98387 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96964, d98387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96964, d98387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96965 q = 1) (hb : d98388 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96965, d98388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96965, d98388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d96966 q = 1) (hb : d98389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96966, d98389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96966, d98389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96967 q = 1) (hb : d98390 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96967, d98390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d96967, d98390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12975 (p : Pattern) (ha : d97059 p = 1) (hb : d98002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97028 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97048 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d96992 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d96993 q = 1) (hb : d97997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96993, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12833 q ha hb
    | true =>
      simp only [d96993, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d97049 q = 1) (hb : d97998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97049, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d97049, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d97055 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d97056 q = 1) (hb : d97999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97056, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97056, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d97057 q = 1) (hb : d98000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97057, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d97057, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97058 q = 1) (hb : d98001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97058, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97058, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d97059 q = 1) (hb : d98002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97059, d98002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97059, d98002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12976 (p : Pattern) (ha : d97081 p = 1) (hb : d98011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97019 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97048 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d96992 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d96993 q = 1) (hb : d97997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96993, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12833 q ha hb
    | true =>
      simp only [d96993, d97997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97049 q = 1) (hb : d97998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97049, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d97049, d97998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97055 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97056 q = 1) (hb : d97999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97056, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97056, d97999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97057 q = 1) (hb : d98000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97057, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97057, d98000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97058 q = 1) (hb : d98001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97058, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97058, d98001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d97065 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d97070 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d97073 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d97002 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d97003 q = 1) (hb : d98006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97003, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12835 q ha hb
    | true =>
      simp only [d97003, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d97074 q = 1) (hb : d98007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97074, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d97074, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d97077 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d97078 q = 1) (hb : d98008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97078, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d97078, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d97079 q = 1) (hb : d98009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97079, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d97079, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d97080 q = 1) (hb : d98010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97080, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d97080, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d97081 q = 1) (hb : d98011 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97081, d98011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97081, d98011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro12977 (p : Pattern) (ha : d97106 p = 1) (hb : d98396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97003 q = 1) (hb : d98006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97003, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12835 q ha hb
    | true =>
      simp only [d97003, d98006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d97074 q = 1) (hb : d98007 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97074, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97074, d98007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d97077 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d97078 q = 1) (hb : d98008 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97078, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97078, d98008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d97104 q = 1) (hb : d98009 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97104, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97104, d98009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97105 q = 1) (hb : d98010 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97105, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97105, d98010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97106 q = 1) (hb : d98396 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97106, d98396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97106, d98396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12978 (p : Pattern) (ha : d97151 p = 1) (hb : d98091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97146 q = 1) (hb : d98086 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97146, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12861 q ha hb
    | true =>
      simp only [d97146, d98086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97147 q = 1) (hb : d98087 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97147, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97147, d98087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97138 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97148 q = 1) (hb : d98088 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97148, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97148, d98088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97149 q = 1) (hb : d98089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97149, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97149, d98089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97150 q = 1) (hb : d98090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97150, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97150, d98090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97151 q = 1) (hb : d98091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97151, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97151, d98091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12979 (p : Pattern) (ha : d97167 p = 1) (hb : d98406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97155 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97156 q = 1) (hb : d98094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97156, d98094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12978 q ha hb
    | true =>
      simp only [d97156, d98094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d97157 q = 1) (hb : d98402 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97157, d98402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97157, d98402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d97163 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d97164 q = 1) (hb : d98403 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97164, d98403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97164, d98403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d97165 q = 1) (hb : d98404 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97165, d98404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97165, d98404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97166 q = 1) (hb : d98405 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97166, d98405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97166, d98405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97167 q = 1) (hb : d98406 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97167, d98406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97167, d98406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12980 (p : Pattern) (ha : d97180 p = 1) (hb : d98412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97082 q = 1) (hb : d98012 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97082, d98012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12975 q ha hb
    | true =>
      simp only [d97082, d98012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12976 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97100 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97101 q = 1) (hb : d98013 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97101, d98013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97101, d98013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d97102 q = 1) (hb : d98394 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97102, d98394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97102, d98394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d97103 q = 1) (hb : d98395 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97103, d98395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97103, d98395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97107 q = 1) (hb : d98397 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97107, d98397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d97107, d98397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12977 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d97109 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d97110 q = 1) (hb : d98398 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97110, d98398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d97110, d98398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d97111 q = 1) (hb : d98399 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97111, d98399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97111, d98399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d97112 q = 1) (hb : d98400 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97112, d98400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97112, d98400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d97113 q = 1) (hb : d98401 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d97113, d98401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97113, d98401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d97168 q = 1) (hb : d98407 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97168, d98407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d97168, d98407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12979 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d97175 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d97176 q = 1) (hb : d98408 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97176, d98408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d97176, d98408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d97177 q = 1) (hb : d98409 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97177, d98409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d97177, d98409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d97178 q = 1) (hb : d98410 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97178, d98410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d97178, d98410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d97179 q = 1) (hb : d98411 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d97179, d98411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d97179, d98411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d97180 q = 1) (hb : d98412 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d97180, d98412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d97180, d98412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro12981 (p : Pattern) (ha : d97186 p = 1) (hb : d98418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97181 q = 1) (hb : d98413 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d97181, d98413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97181, d98413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12980 q ha hb
  have h2 (q : Pattern) (ha : d97182 q = 1) (hb : d98414 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97182, d98414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97182, d98414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97183 q = 1) (hb : d98415 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d97183, d98415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97183, d98415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97184 q = 1) (hb : d98416 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d97184, d98416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97184, d98416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97185 q = 1) (hb : d98417 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d97185, d98417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97185, d98417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97186 q = 1) (hb : d98418 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d97186, d98418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97186, d98418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12982 (p : Pattern) (ha : d97279 p = 1) (hb : d98130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97239 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97248 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97268 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d97212 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d97213 q = 1) (hb : d98125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97213, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12869 q ha hb
    | true =>
      simp only [d97213, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d97269 q = 1) (hb : d98126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97269, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d97269, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d97275 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d97276 q = 1) (hb : d98127 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97276, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97276, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d97277 q = 1) (hb : d98128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97277, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d97277, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97278 q = 1) (hb : d98129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97278, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97278, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d97279 q = 1) (hb : d98130 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97279, d98130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97279, d98130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro12983 (p : Pattern) (ha : d97301 p = 1) (hb : d98139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97239 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97248 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97268 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97212 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97213 q = 1) (hb : d98125 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97213, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12869 q ha hb
    | true =>
      simp only [d97213, d98125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97269 q = 1) (hb : d98126 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97269, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d97269, d98126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d97275 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97276 q = 1) (hb : d98127 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97276, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97276, d98127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d97277 q = 1) (hb : d98128 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97277, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97277, d98128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97278 q = 1) (hb : d98129 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97278, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97278, d98129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d97285 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d97290 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d97293 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d97222 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d97223 q = 1) (hb : d98134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97223, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12871 q ha hb
    | true =>
      simp only [d97223, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d97294 q = 1) (hb : d98135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97294, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d97294, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d97297 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d97298 q = 1) (hb : d98136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97298, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d97298, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d97299 q = 1) (hb : d98137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97299, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d97299, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d97300 q = 1) (hb : d98138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97300, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d97300, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d97301 q = 1) (hb : d98139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97301, d98139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97301, d98139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro12984 (p : Pattern) (ha : d97326 p = 1) (hb : d98425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97293 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97222 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97223 q = 1) (hb : d98134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97223, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12871 q ha hb
    | true =>
      simp only [d97223, d98134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d97294 q = 1) (hb : d98135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97294, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97294, d98135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d97297 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d97298 q = 1) (hb : d98136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97298, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97298, d98136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d97324 q = 1) (hb : d98137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97324, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97324, d98137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97325 q = 1) (hb : d98138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97325, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97325, d98138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97326 q = 1) (hb : d98425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97326, d98425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97326, d98425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12985 (p : Pattern) (ha : d97371 p = 1) (hb : d98219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97366 q = 1) (hb : d98214 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d97366, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12897 q ha hb
    | true =>
      simp only [d97366, d98214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97367 q = 1) (hb : d98215 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d97367, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97367, d98215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97358 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97368 q = 1) (hb : d98216 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d97368, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97368, d98216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d97369 q = 1) (hb : d98217 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d97369, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97369, d98217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97370 q = 1) (hb : d98218 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d97370, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97370, d98218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d97371 q = 1) (hb : d98219 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d97371, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97371, d98219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro12986 (p : Pattern) (ha : d97387 p = 1) (hb : d98435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d97363 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97375 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97376 q = 1) (hb : d98222 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d97376, d98222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12985 q ha hb
    | true =>
      simp only [d97376, d98222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d97377 q = 1) (hb : d98431 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97377, d98431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97377, d98431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d97383 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d97384 q = 1) (hb : d98432 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97384, d98432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97384, d98432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d97385 q = 1) (hb : d98433 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97385, d98433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97385, d98433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97386 q = 1) (hb : d98434 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97386, d98434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97386, d98434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97387 q = 1) (hb : d98435 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97387, d98435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97387, d98435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro12987 (p : Pattern) (ha : d97400 p = 1) (hb : d98441 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d97231 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97302 q = 1) (hb : d98140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97302, d98140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12982 q ha hb
    | true =>
      simp only [d97302, d98140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12983 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97320 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97321 q = 1) (hb : d98141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97321, d98141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97321, d98141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d97322 q = 1) (hb : d98423 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97322, d98423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97322, d98423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d97323 q = 1) (hb : d98424 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97323, d98424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97323, d98424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97327 q = 1) (hb : d98426 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97327, d98426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d97327, d98426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12984 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d97329 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d97330 q = 1) (hb : d98427 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97330, d98427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d97330, d98427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d97331 q = 1) (hb : d98428 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97331, d98428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97331, d98428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d97332 q = 1) (hb : d98429 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97332, d98429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97332, d98429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d97333 q = 1) (hb : d98430 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d97333, d98430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97333, d98430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d97388 q = 1) (hb : d98436 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d97388, d98436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d97388, d98436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12986 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d97395 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d97396 q = 1) (hb : d98437 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d97396, d98437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d97396, d98437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d97397 q = 1) (hb : d98438 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d97397, d98438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d97397, d98438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d97398 q = 1) (hb : d98439 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d97398, d98439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d97398, d98439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d97399 q = 1) (hb : d98440 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d97399, d98440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d97399, d98440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d97400 q = 1) (hb : d98441 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d97400, d98441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d97400, d98441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro12988 (p : Pattern) (ha : d97406 p = 1) (hb : d98447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97401 q = 1) (hb : d98442 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d97401, d98442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97401, d98442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12987 q ha hb
  have h2 (q : Pattern) (ha : d97402 q = 1) (hb : d98443 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97402, d98443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97402, d98443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d97403 q = 1) (hb : d98444 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d97403, d98444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97403, d98444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d97404 q = 1) (hb : d98445 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d97404, d98445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97404, d98445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d97405 q = 1) (hb : d98446 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d97405, d98446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97405, d98446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97406 q = 1) (hb : d98447 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d97406, d98447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d97406, d98447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro12989 (p : Pattern) (ha : d97412 p = 1) (hb : d98453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d96533 q = 1) (hb : d98338 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d96533, d98338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12953 q ha hb
    | true =>
      simp only [d96533, d98338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12960 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d96750 q = 1) (hb : d98364 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d96750, d98364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96750, d98364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12967 q ha hb
  have h3 (q : Pattern) (ha : d96751 q = 1) (hb : d98365 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d96751, d98365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96751, d98365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d96968 q = 1) (hb : d98391 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d96968, d98391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96968, d98391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12974 q ha hb
  have h5 (q : Pattern) (ha : d96969 q = 1) (hb : d98392 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d96969, d98392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d96969, d98392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d96970 q = 1) (hb : d98393 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d96970, d98393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d96970, d98393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97187 q = 1) (hb : d98419 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d97187, d98419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97187, d98419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12981 q ha hb
  have h8 (q : Pattern) (ha : d97188 q = 1) (hb : d98420 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d97188, d98420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97188, d98420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97189 q = 1) (hb : d98421 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d97189, d98421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97189, d98421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97190 q = 1) (hb : d98422 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d97190, d98422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d97190, d98422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d97407 q = 1) (hb : d98448 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d97407, d98448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97407, d98448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12988 q ha hb
  have h12 (q : Pattern) (ha : d97408 q = 1) (hb : d98449 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d97408, d98449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97408, d98449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d97409 q = 1) (hb : d98450 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d97409, d98450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97409, d98450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d97410 q = 1) (hb : d98451 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d97410, d98451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d97410, d98451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d97411 q = 1) (hb : d98452 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d97411, d98452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97411, d98452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d97412 q = 1) (hb : d98453 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d97412, d98453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d97412, d98453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro12990 (p : Pattern) (ha : d97418 p = 1) (hb : d98459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97413 q = 1) (hb : d98454 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d97413, d98454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12989 q ha hb
    | true =>
      simp only [d97413, d98454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97414 q = 1) (hb : d98455 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d97414, d98455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97414, d98455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97415 q = 1) (hb : d98456 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d97415, d98456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97415, d98456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97416 q = 1) (hb : d98457 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d97416, d98457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97416, d98457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97417 q = 1) (hb : d98458 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d97417, d98458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97417, d98458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97418 q = 1) (hb : d98459 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d97418, d98459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97418, d98459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12991 (p : Pattern) (ha : d97424 p = 1) (hb : d98465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97419 q = 1) (hb : d98460 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d97419, d98460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12990 q ha hb
    | true =>
      simp only [d97419, d98460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97420 q = 1) (hb : d98461 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d97420, d98461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97420, d98461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97421 q = 1) (hb : d98462 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d97421, d98462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97421, d98462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97422 q = 1) (hb : d98463 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d97422, d98463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97422, d98463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97423 q = 1) (hb : d98464 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d97423, d98464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97423, d98464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97424 q = 1) (hb : d98465 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d97424, d98465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97424, d98465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12992 (p : Pattern) (ha : d97430 p = 1) (hb : d98471 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97425 q = 1) (hb : d98466 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d97425, d98466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12991 q ha hb
    | true =>
      simp only [d97425, d98466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97426 q = 1) (hb : d98467 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d97426, d98467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97426, d98467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97427 q = 1) (hb : d98468 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d97427, d98468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97427, d98468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97428 q = 1) (hb : d98469 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d97428, d98469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97428, d98469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97429 q = 1) (hb : d98470 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d97429, d98470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97429, d98470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97430 q = 1) (hb : d98471 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d97430, d98471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97430, d98471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12993 (p : Pattern) (ha : d97436 p = 1) (hb : d98477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97431 q = 1) (hb : d98472 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d97431, d98472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12992 q ha hb
    | true =>
      simp only [d97431, d98472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97432 q = 1) (hb : d98473 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d97432, d98473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97432, d98473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97433 q = 1) (hb : d98474 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d97433, d98474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97433, d98474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97434 q = 1) (hb : d98475 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d97434, d98475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97434, d98475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97435 q = 1) (hb : d98476 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d97435, d98476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97435, d98476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97436 q = 1) (hb : d98477 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d97436, d98477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97436, d98477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12994 (p : Pattern) (ha : d97442 p = 1) (hb : d98483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97437 q = 1) (hb : d98478 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d97437, d98478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12993 q ha hb
    | true =>
      simp only [d97437, d98478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97438 q = 1) (hb : d98479 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d97438, d98479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97438, d98479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97439 q = 1) (hb : d98480 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d97439, d98480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97439, d98480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97440 q = 1) (hb : d98481 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d97440, d98481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97440, d98481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97441 q = 1) (hb : d98482 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d97441, d98482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97441, d98482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97442 q = 1) (hb : d98483 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d97442, d98483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97442, d98483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12995 (p : Pattern) (ha : d97448 p = 1) (hb : d98489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97443 q = 1) (hb : d98484 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d97443, d98484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12994 q ha hb
    | true =>
      simp only [d97443, d98484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97444 q = 1) (hb : d98485 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d97444, d98485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97444, d98485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97445 q = 1) (hb : d98486 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d97445, d98486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97445, d98486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97446 q = 1) (hb : d98487 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d97446, d98487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97446, d98487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97447 q = 1) (hb : d98488 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d97447, d98488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97447, d98488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97448 q = 1) (hb : d98489 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d97448, d98489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97448, d98489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12996 (p : Pattern) (ha : d97454 p = 1) (hb : d98495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d97449 q = 1) (hb : d98490 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d97449, d98490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12995 q ha hb
    | true =>
      simp only [d97449, d98490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d97450 q = 1) (hb : d98491 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d97450, d98491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97450, d98491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d97451 q = 1) (hb : d98492 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d97451, d98492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97451, d98492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d97452 q = 1) (hb : d98493 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d97452, d98493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97452, d98493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d97453 q = 1) (hb : d98494 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d97453, d98494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97453, d98494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d97454 q = 1) (hb : d98495 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d97454, d98495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97454, d98495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro12997 (p : Pattern) (ha : d97517 p = 1) (hb : d98500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94839 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94845 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d94857 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d97513 q = 1) (hb : d98496 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97513, d98496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97513, d98496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d94769 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d97514 q = 1) (hb : d98497 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97514, d98497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d97514, d98497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97515 q = 1) (hb : d98498 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97515, d98498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97515, d98498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d97516 q = 1) (hb : d98499 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97516, d98499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97516, d98499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d97517 q = 1) (hb : d98500 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97517, d98500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97517, d98500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro12998 (p : Pattern) (ha : d97524 p = 1) (hb : d98505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d94839 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d94857 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d97464 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d97513 q = 1) (hb : d98496 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97513, d98496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d97513, d98496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d94769 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d97514 q = 1) (hb : d98497 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97514, d98497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d97514, d98497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97515 q = 1) (hb : d98498 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97515, d98498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97515, d98498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d97516 q = 1) (hb : d98499 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97516, d98499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97516, d98499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d94879 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d94883 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d94885 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d97520 q = 1) (hb : d98501 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97520, d98501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d97520, d98501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d94776 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d97521 q = 1) (hb : d98502 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97521, d98502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d97521, d98502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d97522 q = 1) (hb : d98503 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97522, d98503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d97522, d98503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d97523 q = 1) (hb : d98504 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97523, d98504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d97523, d98504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d97524 q = 1) (hb : d98505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d97524, d98505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d97524, d98505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro12999 (p : Pattern) (ha : d98290 p = 1) (hb : d98512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d94885 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d97471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d97520 q = 1) (hb : d98501 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d97520, d98501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d97520, d98501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d94776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d97521 q = 1) (hb : d98502 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d97521, d98502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d97521, d98502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d97522 q = 1) (hb : d98510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d97522, d98510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97522, d98510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d97523 q = 1) (hb : d98511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d97523, d98511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97523, d98511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d98290 q = 1) (hb : d98512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d98290, d98512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98290, d98512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
