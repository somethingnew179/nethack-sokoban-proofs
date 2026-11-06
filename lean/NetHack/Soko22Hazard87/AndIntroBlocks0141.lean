import NetHack.Soko22Hazard87.AndIntroBlocks0140
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro35250 (p : Pattern) (ha : d14497 p = 1) (hb : d142666 p = 1) : d168152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d142666 q = 1) : d168147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35248 q ha hb
    | true =>
      simp only [d14492, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35249 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d142666 q = 1) : d168148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d142666 q = 1) : d168149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d142666 q = 1) : d168150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d142666 q = 1) : d168151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14497 q = 1) (hb : d142666 q = 1) : d168152 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14497, d168152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14497, d168152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35251 (p : Pattern) (ha : d14500 p = 1) (hb : d142666 p = 1) : d168155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d142666 q = 1) : d168143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d142666 q = 1) : d168144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14486 q = 1) (hb : d142666 q = 1) : d168145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14486, d168145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14486, d168145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14500 q = 1) (hb : d142666 q = 1) : d168155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14500, d168155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14500, d168155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35252 (p : Pattern) (ha : d14501 p = 1) (hb : d142666 p = 1) : d120426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d142666 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14490 q = 1) (hb : d142666 q = 1) : d120415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14490, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14490, d120415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14501 q = 1) (hb : d142666 q = 1) : d120426 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14501, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14501, d120426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35253 (p : Pattern) (ha : d14507 p = 1) (hb : d142666 p = 1) : d168161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d142666 q = 1) : d168147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35248 q ha hb
    | true =>
      simp only [d14492, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35249 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d142666 q = 1) : d168148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d142666 q = 1) : d168149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d142666 q = 1) : d168150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d142666 q = 1) : d168151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14502 q = 1) (hb : d142666 q = 1) : d168156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35251 q ha hb
    | true =>
      simp only [d14502, d168156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35252 q ha hb
  have h7 (q : Pattern) (ha : d14503 q = 1) (hb : d142666 q = 1) : d168157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, d168157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14504 q = 1) (hb : d142666 q = 1) : d168158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14504, d168158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14505 q = 1) (hb : d142666 q = 1) : d168159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d168159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14506 q = 1) (hb : d142666 q = 1) : d168160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d168160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14507 q = 1) (hb : d142666 q = 1) : d168161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14507, d168161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14507, d168161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35254 (p : Pattern) (ha : d14622 p = 1) (hb : d142666 p = 1) : d168222 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14492 q = 1) (hb : d142666 q = 1) : d168147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14492, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35248 q ha hb
    | true =>
      simp only [d14492, d168147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35249 q ha hb
  have h2 (q : Pattern) (ha : d14493 q = 1) (hb : d142666 q = 1) : d168148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14493, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14493, d168148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14494 q = 1) (hb : d142666 q = 1) : d168149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14494, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14494, d168149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14495 q = 1) (hb : d142666 q = 1) : d168150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14495, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14495, d168150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14496 q = 1) (hb : d142666 q = 1) : d168151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14496, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14496, d168151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14617 q = 1) (hb : d142666 q = 1) : d120514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35249 q ha hb
    | true =>
      simp only [d14617, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14618 q = 1) (hb : d142666 q = 1) : d120515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14619 q = 1) (hb : d142666 q = 1) : d120516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14619, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14620 q = 1) (hb : d142666 q = 1) : d120517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14621 q = 1) (hb : d142666 q = 1) : d120518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14622 q = 1) (hb : d142666 q = 1) : d168222 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14622, d168222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14622, d168222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35255 (p : Pattern) (ha : d14628 p = 1) (hb : d142666 p = 1) : d120525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14617 q = 1) (hb : d142666 q = 1) : d120514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14617, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35249 q ha hb
    | true =>
      simp only [d14617, d120514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14618 q = 1) (hb : d142666 q = 1) : d120515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14618, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14618, d120515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14619 q = 1) (hb : d142666 q = 1) : d120516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14619, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14619, d120516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14620 q = 1) (hb : d142666 q = 1) : d120517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14620, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14620, d120517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14621 q = 1) (hb : d142666 q = 1) : d120518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14621, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14621, d120518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14623 q = 1) (hb : d142666 q = 1) : d120520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35252 q ha hb
    | true =>
      simp only [d14623, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14624 q = 1) (hb : d142666 q = 1) : d120521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14625 q = 1) (hb : d142666 q = 1) : d120522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14625, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14626 q = 1) (hb : d142666 q = 1) : d120523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14627 q = 1) (hb : d142666 q = 1) : d120524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14628 q = 1) (hb : d142666 q = 1) : d120525 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14628, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14628, d120525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35256 (p : Pattern) (ha : d14637 p = 1) (hb : d142666 p = 1) : d120534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14623 q = 1) (hb : d142666 q = 1) : d120520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14623, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35252 q ha hb
    | true =>
      simp only [d14623, d120520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14624 q = 1) (hb : d142666 q = 1) : d120521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14624, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14624, d120521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14625 q = 1) (hb : d142666 q = 1) : d120522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14625, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14625, d120522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14626 q = 1) (hb : d142666 q = 1) : d120523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14626, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14626, d120523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14627 q = 1) (hb : d142666 q = 1) : d120524 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14627, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14627, d120524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14637 q = 1) (hb : d142666 q = 1) : d120534 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14637, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14637, d120534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35257 (p : Pattern) (ha : d14658 p = 1) (hb : d142665 p = 1) : d120545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14154 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d980 q = 1) (hb : d122304 q = 1) : d980 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14658 q = 1) (hb : d142665 q = 1) : d120545 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14658, d142665, d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14658, d142665, d120545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35258 (p : Pattern) (ha : d14680 p = 1) (hb : d142666 p = 1) : d120567 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14662 q = 1) (hb : d142666 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35257 q ha hb
    | true =>
      simp only [d14662, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14663 q = 1) (hb : d142666 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14664 q = 1) (hb : d142666 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14670 q = 1) (hb : d142666 q = 1) : d120565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14670, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14679 q = 1) (hb : d142666 q = 1) : d120566 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14679, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14679, d120566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14680 q = 1) (hb : d142666 q = 1) : d120567 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14680, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14680, d120567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35259 (p : Pattern) (ha : d14736 p = 1) (hb : d142666 p = 1) : d120594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14681 q = 1) (hb : d142666 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35258 q ha hb
    | true =>
      simp only [d14681, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14682 q = 1) (hb : d142666 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14733 q = 1) (hb : d142666 q = 1) : d120591 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14733, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14733, d120591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14734 q = 1) (hb : d142666 q = 1) : d120592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14734, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14734, d120592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14735 q = 1) (hb : d142666 q = 1) : d120593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14735, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14735, d120593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14736 q = 1) (hb : d142666 q = 1) : d120594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14736, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14736, d120594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35260 (p : Pattern) (ha : d14742 p = 1) (hb : d142666 p = 1) : d120600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14737 q = 1) (hb : d142666 q = 1) : d120595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14737, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35259 q ha hb
    | true =>
      simp only [d14737, d120595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14738 q = 1) (hb : d142666 q = 1) : d120596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14738, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14738, d120596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14739 q = 1) (hb : d142666 q = 1) : d120597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14739, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14739, d120597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14740 q = 1) (hb : d142666 q = 1) : d120598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14740, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14740, d120598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14741 q = 1) (hb : d142666 q = 1) : d120599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14741, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14741, d120599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14742 q = 1) (hb : d142666 q = 1) : d120600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14742, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14742, d120600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35261 (p : Pattern) (ha : d14512 p = 1) (hb : d142666 p = 1) : d168166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d142666 q = 1) : d168143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d142666 q = 1) : d168144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d142666 q = 1) : d168165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, d168165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, d168165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14512 q = 1) (hb : d142666 q = 1) : d168166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14512, d168166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14512, d168166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35262 (p : Pattern) (ha : d14514 p = 1) (hb : d142666 p = 1) : d120439 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d142666 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d142666 q = 1) : d120438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14514 q = 1) (hb : d142666 q = 1) : d120439 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14514, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14514, d120439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35263 (p : Pattern) (ha : d14521 p = 1) (hb : d142666 p = 1) : d168173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d142666 q = 1) : d168143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d142666 q = 1) : d168171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, d168171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, d168171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d142666 q = 1) : d168172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, d168172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, d168172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14521 q = 1) (hb : d142666 q = 1) : d168173 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14521, d168173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14521, d168173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35264 (p : Pattern) (ha : d14524 p = 1) (hb : d142666 p = 1) : d120449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d142666 q = 1) : d120447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d142666 q = 1) : d120448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14524 q = 1) (hb : d142666 q = 1) : d120449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14524, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14524, d120449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35265 (p : Pattern) (ha : d14532 p = 1) (hb : d142665 p = 1) : d168177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14528 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14531 q = 1) (hb : d122304 q = 1) : d14531 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14532 q = 1) (hb : d142665 q = 1) : d168177 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14532, d142665, d168177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14532, d142665, d168177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35266 (p : Pattern) (ha : d14542 p = 1) (hb : d142666 p = 1) : d168183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14263 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14533 q = 1) (hb : d142666 q = 1) : d168178 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14533, d142666, d168178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35265 q ha hb
    | true =>
      simp only [d14533, d142666, d168178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14534 q = 1) (hb : d142666 q = 1) : d168179 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14534, d168179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14534, d168179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14535 q = 1) (hb : d142666 q = 1) : d168180 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14535, d168180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14535, d168180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14536 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14537 q = 1) (hb : d142666 q = 1) : d168043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14537, d142666, d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35223 q ha hb
    | true =>
      simp only [d14537, d142666, d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d14538 q = 1) (hb : d142666 q = 1) : d168044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14538, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14538, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14539 q = 1) (hb : d142666 q = 1) : d168045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14539, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14539, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14540 q = 1) (hb : d142666 q = 1) : d168181 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14540, d168181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14540, d168181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14467 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14468 q = 1) (hb : d142666 q = 1) : d168043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14468, d142666, d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35223 q ha hb
    | true =>
      simp only [d14468, d142666, d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d14469 q = 1) (hb : d142666 q = 1) : d168044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14469, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14469, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14470 q = 1) (hb : d142666 q = 1) : d168045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14470, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14470, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14471 q = 1) (hb : d142666 q = 1) : d120397 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14471, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35245 q ha hb
    | true =>
      simp only [d14471, d142666, d120397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d14472 q = 1) (hb : d142666 q = 1) : d120398 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14472, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14472, d120398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14473 q = 1) (hb : d142666 q = 1) : d120399 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14473, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14473, d120399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14474 q = 1) (hb : d142666 q = 1) : d168138 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14474, d168138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14474, d168138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14541 q = 1) (hb : d142666 q = 1) : d168182 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14541, d168182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14541, d168182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14542 q = 1) (hb : d142666 q = 1) : d168183 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14542, d168183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d14542, d168183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro35267 (p : Pattern) (ha : d14548 p = 1) (hb : d142666 p = 1) : d168189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d142666 q = 1) : d168184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, d168184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35266 q ha hb
    | true =>
      simp only [d14543, d168184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d142666 q = 1) : d168185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, d168185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, d168185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d142666 q = 1) : d168186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, d168186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, d168186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d142666 q = 1) : d168187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, d168187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, d168187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d142666 q = 1) : d168188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, d168188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, d168188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14548 q = 1) (hb : d142666 q = 1) : d168189 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14548, d168189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14548, d168189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35268 (p : Pattern) (ha : d14585 p = 1) (hb : d142666 p = 1) : d168195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d142666 q = 1) : d168192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, d168192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, d168192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d142666 q = 1) : d168193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, d168193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, d168193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d142666 q = 1) : d168194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, d168194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, d168194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14585 q = 1) (hb : d142666 q = 1) : d168195 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14585, d168195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14585, d168195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35269 (p : Pattern) (ha : d125534 p = 1) (hb : d142666 p = 1) : d168201 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d142666 q = 1) : d168167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, d168167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35261 q ha hb
    | true =>
      simp only [d14515, d168167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35262 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d142666 q = 1) : d168168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, d168168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, d168168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d142666 q = 1) : d168169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, d168169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, d168169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d142666 q = 1) : d168170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, d168170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, d168170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d142666 q = 1) : d168174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, d168174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35263 q ha hb
    | true =>
      simp only [d14525, d168174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35264 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d142666 q = 1) : d168175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, d168175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, d168175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d142666 q = 1) : d168176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, d168176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, d168176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d142666 q = 1) : d168190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, d168190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35267 q ha hb
    | true =>
      simp only [d14549, d168190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35248 q ha hb
  have h9 (q : Pattern) (ha : d125530 q = 1) (hb : d142666 q = 1) : d168191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d168191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125530, d168191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d142666 q = 1) : d168196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, d168196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35268 q ha hb
    | true =>
      simp only [d14586, d168196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d142666 q = 1) : d168197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, d168197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, d168197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125531 q = 1) (hb : d142666 q = 1) : d168198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d168198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, d168198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125532 q = 1) (hb : d142666 q = 1) : d168199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d168199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125532, d168199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125533 q = 1) (hb : d142666 q = 1) : d168200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d168200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125533, d168200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125534 q = 1) (hb : d142666 q = 1) : d168201 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125534, d168201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125534, d168201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35270 (p : Pattern) (ha : d14592 p = 1) (hb : d142666 p = 1) : d168202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d142666 q = 1) : d168143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14485 q = 1) (hb : d142666 q = 1) : d168144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14485, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14485, d168144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14511 q = 1) (hb : d142666 q = 1) : d168165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14511, d168165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14511, d168165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14592 q = 1) (hb : d142666 q = 1) : d168202 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14592, d168202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14592, d168202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35271 (p : Pattern) (ha : d14593 p = 1) (hb : d142666 p = 1) : d120487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14489 q = 1) (hb : d142666 q = 1) : d120414 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14489, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14489, d120414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14513 q = 1) (hb : d142666 q = 1) : d120438 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14513, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14513, d120438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14593 q = 1) (hb : d142666 q = 1) : d120487 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14593, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14593, d120487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35272 (p : Pattern) (ha : d14598 p = 1) (hb : d142666 p = 1) : d168207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14484 q = 1) (hb : d142666 q = 1) : d168143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14484, d168143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14519 q = 1) (hb : d142666 q = 1) : d168171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14519, d168171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14519, d168171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14520 q = 1) (hb : d142666 q = 1) : d168172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14520, d168172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14520, d168172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14598 q = 1) (hb : d142666 q = 1) : d168207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14598, d168207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14598, d168207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35273 (p : Pattern) (ha : d14599 p = 1) (hb : d142666 p = 1) : d120493 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14482 q = 1) (hb : d142666 q = 1) : d120407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35247 q ha hb
    | true =>
      simp only [d14482, d120407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14483 q = 1) (hb : d142666 q = 1) : d120408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14483, d120408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14488 q = 1) (hb : d142666 q = 1) : d120413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14488, d120413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14522 q = 1) (hb : d142666 q = 1) : d120447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14522, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14522, d120447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14523 q = 1) (hb : d142666 q = 1) : d120448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14523, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14523, d120448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14599 q = 1) (hb : d142666 q = 1) : d120493 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14599, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14599, d120493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35274 (p : Pattern) (ha : d14603 p = 1) (hb : d142666 p = 1) : d168211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14543 q = 1) (hb : d142666 q = 1) : d168184 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14543, d168184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35266 q ha hb
    | true =>
      simp only [d14543, d168184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14544 q = 1) (hb : d142666 q = 1) : d168185 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14544, d168185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14544, d168185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14545 q = 1) (hb : d142666 q = 1) : d168186 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14545, d168186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14545, d168186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14546 q = 1) (hb : d142666 q = 1) : d168187 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14546, d168187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14546, d168187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14547 q = 1) (hb : d142666 q = 1) : d168188 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14547, d168188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14547, d168188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14603 q = 1) (hb : d142666 q = 1) : d168211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14603, d168211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14603, d168211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35275 (p : Pattern) (ha : d14609 p = 1) (hb : d142666 p = 1) : d168214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14478 q = 1) (hb : d142666 q = 1) : d168141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35246 q ha hb
    | true =>
      simp only [d14478, d168141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14479 q = 1) (hb : d142666 q = 1) : d168142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14479, d168142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14582 q = 1) (hb : d142666 q = 1) : d168192 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14582, d168192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14582, d168192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14583 q = 1) (hb : d142666 q = 1) : d168193 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14583, d168193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14583, d168193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14584 q = 1) (hb : d142666 q = 1) : d168194 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14584, d168194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14584, d168194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14609 q = 1) (hb : d142666 q = 1) : d168214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14609, d168214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14609, d168214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35276 (p : Pattern) (ha : d125539 p = 1) (hb : d142666 p = 1) : d168220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14515 q = 1) (hb : d142666 q = 1) : d168167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14515, d168167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35261 q ha hb
    | true =>
      simp only [d14515, d168167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35262 q ha hb
  have h2 (q : Pattern) (ha : d14516 q = 1) (hb : d142666 q = 1) : d168168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14516, d168168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14516, d168168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14517 q = 1) (hb : d142666 q = 1) : d168169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14517, d168169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14517, d168169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14518 q = 1) (hb : d142666 q = 1) : d168170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14518, d168170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14518, d168170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14525 q = 1) (hb : d142666 q = 1) : d168174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14525, d168174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35263 q ha hb
    | true =>
      simp only [d14525, d168174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35264 q ha hb
  have h6 (q : Pattern) (ha : d14526 q = 1) (hb : d142666 q = 1) : d168175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14526, d168175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14526, d168175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14527 q = 1) (hb : d142666 q = 1) : d168176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14527, d168176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14527, d168176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14549 q = 1) (hb : d142666 q = 1) : d168190 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14549, d168190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35267 q ha hb
    | true =>
      simp only [d14549, d168190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35248 q ha hb
  have h9 (q : Pattern) (ha : d125530 q = 1) (hb : d142666 q = 1) : d168191 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125530, d168191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125530, d168191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14586 q = 1) (hb : d142666 q = 1) : d168196 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14586, d168196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35268 q ha hb
    | true =>
      simp only [d14586, d168196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14587 q = 1) (hb : d142666 q = 1) : d168197 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14587, d168197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14587, d168197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125531 q = 1) (hb : d142666 q = 1) : d168198 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125531, d168198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125531, d168198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125532 q = 1) (hb : d142666 q = 1) : d168199 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125532, d168199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125532, d168199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125533 q = 1) (hb : d142666 q = 1) : d168200 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125533, d168200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125533, d168200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14594 q = 1) (hb : d142666 q = 1) : d168203 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14594, d168203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35270 q ha hb
    | true =>
      simp only [d14594, d168203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35271 q ha hb
  have h16 (q : Pattern) (ha : d14595 q = 1) (hb : d142666 q = 1) : d168204 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14595, d168204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14595, d168204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14596 q = 1) (hb : d142666 q = 1) : d168205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14596, d168205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14596, d168205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14597 q = 1) (hb : d142666 q = 1) : d168206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14597, d168206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14597, d168206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14600 q = 1) (hb : d142666 q = 1) : d168208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14600, d168208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35272 q ha hb
    | true =>
      simp only [d14600, d168208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35273 q ha hb
  have h20 (q : Pattern) (ha : d14601 q = 1) (hb : d142666 q = 1) : d168209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14601, d168209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14601, d168209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14602 q = 1) (hb : d142666 q = 1) : d168210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14602, d168210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14602, d168210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14604 q = 1) (hb : d142666 q = 1) : d168212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, d168212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35274 q ha hb
    | true =>
      simp only [d14604, d168212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35251 q ha hb
  have h23 (q : Pattern) (ha : d125535 q = 1) (hb : d142666 q = 1) : d168213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d168213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125535, d168213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14610 q = 1) (hb : d142666 q = 1) : d168215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, d168215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35275 q ha hb
    | true =>
      simp only [d14610, d168215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14611 q = 1) (hb : d142666 q = 1) : d168216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, d168216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14611, d168216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125536 q = 1) (hb : d142666 q = 1) : d168217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d168217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125536, d168217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125537 q = 1) (hb : d142666 q = 1) : d168218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125537, d168218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125537, d168218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125538 q = 1) (hb : d142666 q = 1) : d168219 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125538, d168219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125538, d168219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125539 q = 1) (hb : d142666 q = 1) : d168220 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125539, d168220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125539, d168220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro35277 (p : Pattern) (ha : d125546 p = 1) (hb : d142666 p = 1) : d168229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14604 q = 1) (hb : d142666 q = 1) : d168212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14604, d168212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35274 q ha hb
    | true =>
      simp only [d14604, d168212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35251 q ha hb
  have h2 (q : Pattern) (ha : d125535 q = 1) (hb : d142666 q = 1) : d168213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125535, d168213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125535, d168213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14610 q = 1) (hb : d142666 q = 1) : d168215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14610, d168215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35275 q ha hb
    | true =>
      simp only [d14610, d168215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14611 q = 1) (hb : d142666 q = 1) : d168216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14611, d168216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14611, d168216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125536 q = 1) (hb : d142666 q = 1) : d168217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125536, d168217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125536, d168217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125544 q = 1) (hb : d142666 q = 1) : d168227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125544, d168227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125544, d168227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125545 q = 1) (hb : d142666 q = 1) : d168228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125545, d168228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125545, d168228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125546 q = 1) (hb : d142666 q = 1) : d168229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125546, d168229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125546, d168229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35278 (p : Pattern) (ha : d14649 p = 1) (hb : d142665 p = 1) : d168235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14643 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14648 q = 1) (hb : d122304 q = 1) : d14648 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14649 q = 1) (hb : d142665 q = 1) : d168235 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14649, d142665, d168235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14649, d142665, d168235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35279 (p : Pattern) (ha : d14667 p = 1) (hb : d142666 p = 1) : d168242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14372 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14650 q = 1) (hb : d142666 q = 1) : d168236 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14650, d142666, d168236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35278 q ha hb
    | true =>
      simp only [d14650, d142666, d168236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14651 q = 1) (hb : d142666 q = 1) : d168237 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14651, d168237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14651, d168237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14652 q = 1) (hb : d142666 q = 1) : d168238 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14652, d168238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14652, d168238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14653 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14654 q = 1) (hb : d142666 q = 1) : d168101 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14654, d142666, d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35236 q ha hb
    | true =>
      simp only [d14654, d142666, d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d14655 q = 1) (hb : d142666 q = 1) : d168102 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14655, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14655, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14656 q = 1) (hb : d142666 q = 1) : d168103 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14656, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14656, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14657 q = 1) (hb : d142666 q = 1) : d168239 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14657, d168239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14657, d168239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14658 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14659 q = 1) (hb : d142666 q = 1) : d168101 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, d142666, d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35236 q ha hb
    | true =>
      simp only [d14659, d142666, d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d14660 q = 1) (hb : d142666 q = 1) : d168102 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14660, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14661 q = 1) (hb : d142666 q = 1) : d168103 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14662 q = 1) (hb : d142666 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35257 q ha hb
    | true =>
      simp only [d14662, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d14663 q = 1) (hb : d142666 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14664 q = 1) (hb : d142666 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14665 q = 1) (hb : d142666 q = 1) : d168240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, d168240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14665, d168240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14666 q = 1) (hb : d142666 q = 1) : d168241 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14666, d168241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14666, d168241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14667 q = 1) (hb : d142666 q = 1) : d168242 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14667, d168242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d14667, d168242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro35280 (p : Pattern) (ha : d14672 p = 1) (hb : d142666 p = 1) : d168246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14659 q = 1) (hb : d142666 q = 1) : d168101 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14659, d142666, d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35236 q ha hb
    | true =>
      simp only [d14659, d142666, d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14660 q = 1) (hb : d142666 q = 1) : d168102 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14660, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14660, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14661 q = 1) (hb : d142666 q = 1) : d168103 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14661, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14661, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14662 q = 1) (hb : d142666 q = 1) : d120562 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14662, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35257 q ha hb
    | true =>
      simp only [d14662, d142666, d120562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d14663 q = 1) (hb : d142666 q = 1) : d120563 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14663, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14663, d120563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14664 q = 1) (hb : d142666 q = 1) : d120564 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14664, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14664, d120564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14665 q = 1) (hb : d142666 q = 1) : d168240 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14665, d168240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14665, d168240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14670 q = 1) (hb : d142666 q = 1) : d120565 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14670, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14670, d120565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14671 q = 1) (hb : d142666 q = 1) : d168245 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14671, d168245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14671, d168245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14672 q = 1) (hb : d142666 q = 1) : d168246 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14672, d168246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14672, d168246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro35281 (p : Pattern) (ha : d14678 p = 1) (hb : d142666 p = 1) : d168252 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14668 q = 1) (hb : d142666 q = 1) : d168243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14668, d168243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35279 q ha hb
    | true =>
      simp only [d14668, d168243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14669 q = 1) (hb : d142666 q = 1) : d168244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14669, d168244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14669, d168244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14673 q = 1) (hb : d142666 q = 1) : d168247 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35280 q ha hb
    | true =>
      simp only [d14673, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14674 q = 1) (hb : d142666 q = 1) : d168248 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14675 q = 1) (hb : d142666 q = 1) : d168249 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14675, d168249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14675, d168249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14676 q = 1) (hb : d142666 q = 1) : d168250 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14676, d168250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14676, d168250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14677 q = 1) (hb : d142666 q = 1) : d168251 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14677, d168251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14677, d168251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14678 q = 1) (hb : d142666 q = 1) : d168252 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14678, d168252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14678, d168252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35282 (p : Pattern) (ha : d14686 p = 1) (hb : d142666 p = 1) : d168256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d142666 q = 1) : d168247 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35280 q ha hb
    | true =>
      simp only [d14673, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d142666 q = 1) : d168248 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14681 q = 1) (hb : d142666 q = 1) : d120568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14681, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35258 q ha hb
    | true =>
      simp only [d14681, d120568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14682 q = 1) (hb : d142666 q = 1) : d120569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14682, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14682, d120569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14683 q = 1) (hb : d142666 q = 1) : d168253 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14683, d168253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14683, d168253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14684 q = 1) (hb : d142666 q = 1) : d168254 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14684, d168254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14684, d168254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14685 q = 1) (hb : d142666 q = 1) : d168255 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14685, d168255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14685, d168255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14686 q = 1) (hb : d142666 q = 1) : d168256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14686, d168256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14686, d168256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35283 (p : Pattern) (ha : d14725 p = 1) (hb : d142666 p = 1) : d168262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14673 q = 1) (hb : d142666 q = 1) : d168247 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14673, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35280 q ha hb
    | true =>
      simp only [d14673, d168247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14674 q = 1) (hb : d142666 q = 1) : d168248 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14674, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14674, d168248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14722 q = 1) (hb : d142666 q = 1) : d168259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14722, d168259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14722, d168259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14723 q = 1) (hb : d142666 q = 1) : d168260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14723, d168260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14723, d168260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14724 q = 1) (hb : d142666 q = 1) : d168261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14724, d168261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14724, d168261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14725 q = 1) (hb : d142666 q = 1) : d168262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14725, d168262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14725, d168262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35284 (p : Pattern) (ha : d125556 p = 1) (hb : d142666 p = 1) : d168268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14687 q = 1) (hb : d142666 q = 1) : d168257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14687, d168257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35281 q ha hb
    | true =>
      simp only [d14687, d168257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35282 q ha hb
  have h2 (q : Pattern) (ha : d125552 q = 1) (hb : d142666 q = 1) : d168258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125552, d168258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125552, d168258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14726 q = 1) (hb : d142666 q = 1) : d168263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14726, d168263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35283 q ha hb
    | true =>
      simp only [d14726, d168263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14727 q = 1) (hb : d142666 q = 1) : d168264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14727, d168264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14727, d168264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125553 q = 1) (hb : d142666 q = 1) : d168265 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125553, d168265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125553, d168265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125554 q = 1) (hb : d142666 q = 1) : d168266 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125554, d168266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125554, d168266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125555 q = 1) (hb : d142666 q = 1) : d168267 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125555, d168267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125555, d168267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125556 q = 1) (hb : d142666 q = 1) : d168268 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125556, d168268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125556, d168268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35285 (p : Pattern) (ha : d125562 p = 1) (hb : d142666 p = 1) : d168274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14498 q = 1) (hb : d142666 q = 1) : d168153 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14498, d168153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14498, d168153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35250 q ha hb
  have h2 (q : Pattern) (ha : d14499 q = 1) (hb : d142666 q = 1) : d168154 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14499, d168154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14499, d168154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14508 q = 1) (hb : d142666 q = 1) : d168162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d168162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35250 q ha hb
    | true =>
      simp only [d14508, d168162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35253 q ha hb
  have h4 (q : Pattern) (ha : d14509 q = 1) (hb : d142666 q = 1) : d168163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d168163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14509, d168163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14510 q = 1) (hb : d142666 q = 1) : d168164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14510, d168164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14510, d168164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125540 q = 1) (hb : d142666 q = 1) : d168221 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125540, d168221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35269 q ha hb
    | true =>
      simp only [d125540, d168221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35276 q ha hb
  have h7 (q : Pattern) (ha : d14629 q = 1) (hb : d142666 q = 1) : d168223 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14629, d168223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35254 q ha hb
    | true =>
      simp only [d14629, d168223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35255 q ha hb
  have h8 (q : Pattern) (ha : d125541 q = 1) (hb : d142666 q = 1) : d168224 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125541, d168224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125541, d168224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125542 q = 1) (hb : d142666 q = 1) : d168225 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125542, d168225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125542, d168225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125543 q = 1) (hb : d142666 q = 1) : d168226 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125543, d168226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125543, d168226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125547 q = 1) (hb : d142666 q = 1) : d168230 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125547, d168230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125547, d168230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35277 q ha hb
  have h12 (q : Pattern) (ha : d14638 q = 1) (hb : d142666 q = 1) : d120535 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14638, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14638, d120535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35256 q ha hb
  have h13 (q : Pattern) (ha : d125548 q = 1) (hb : d142666 q = 1) : d168231 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125548, d168231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125548, d168231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125549 q = 1) (hb : d142666 q = 1) : d168232 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125549, d168232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125549, d168232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125550 q = 1) (hb : d142666 q = 1) : d168233 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125550, d168233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125550, d168233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125551 q = 1) (hb : d142666 q = 1) : d168234 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125551, d168234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125551, d168234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125557 q = 1) (hb : d142666 q = 1) : d168269 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125557, d168269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125557, d168269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35284 q ha hb
  have h18 (q : Pattern) (ha : d14743 q = 1) (hb : d142666 q = 1) : d120601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14743, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14743, d120601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35260 q ha hb
  have h19 (q : Pattern) (ha : d125558 q = 1) (hb : d142666 q = 1) : d168270 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125558, d168270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125558, d168270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125559 q = 1) (hb : d142666 q = 1) : d168271 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125559, d168271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125559, d168271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125560 q = 1) (hb : d142666 q = 1) : d168272 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125560, d168272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125560, d168272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125561 q = 1) (hb : d142666 q = 1) : d168273 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125561, d168273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125561, d168273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125562 q = 1) (hb : d142666 q = 1) : d168274 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125562, d168274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125562, d168274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35286 (p : Pattern) (ha : d125568 p = 1) (hb : d142666 p = 1) : d168280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125563 q = 1) (hb : d142666 q = 1) : d168275 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125563, d168275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125563, d168275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35285 q ha hb
  have h2 (q : Pattern) (ha : d125564 q = 1) (hb : d142666 q = 1) : d168276 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125564, d168276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125564, d168276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125565 q = 1) (hb : d142666 q = 1) : d168277 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125565, d168277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125565, d168277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125566 q = 1) (hb : d142666 q = 1) : d168278 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125566, d168278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125566, d168278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125567 q = 1) (hb : d142666 q = 1) : d168279 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125567, d168279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125567, d168279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125568 q = 1) (hb : d142666 q = 1) : d168280 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125568, d168280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125568, d168280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35287 (p : Pattern) (ha : d14761 p = 1) (hb : d142665 p = 1) : d168283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14757 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14760 q = 1) (hb : d122304 q = 1) : d14760 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14761 q = 1) (hb : d142665 q = 1) : d168283 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14761, d142665, d168283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14761, d142665, d168283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35288 (p : Pattern) (ha : d14766 p = 1) (hb : d142665 p = 1) : d168287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14762 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14765 q = 1) (hb : d122304 q = 1) : d14765 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14766 q = 1) (hb : d142665 q = 1) : d168287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14766, d142665, d168287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14766, d142665, d168287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35289 (p : Pattern) (ha : d14784 p = 1) (hb : d142666 p = 1) : d168294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14767 q = 1) (hb : d142666 q = 1) : d168284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35287 q ha hb
    | true =>
      simp only [d14767, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14768 q = 1) (hb : d142666 q = 1) : d168285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14769 q = 1) (hb : d142666 q = 1) : d168286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14773 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14774 q = 1) (hb : d142666 q = 1) : d168288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35288 q ha hb
    | true =>
      simp only [d14774, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d14775 q = 1) (hb : d142666 q = 1) : d168289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14776 q = 1) (hb : d142666 q = 1) : d168290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14777 q = 1) (hb : d142666 q = 1) : d168291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14777, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14778 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14779 q = 1) (hb : d142666 q = 1) : d168288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14779, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35288 q ha hb
    | true =>
      simp only [d14779, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d14780 q = 1) (hb : d142666 q = 1) : d168289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14780, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14780, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14781 q = 1) (hb : d142666 q = 1) : d168290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14782 q = 1) (hb : d142666 q = 1) : d168292 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14782, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d14783 q = 1) (hb : d142666 q = 1) : d168293 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14783, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14783, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14784 q = 1) (hb : d142666 q = 1) : d168294 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14784, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14784, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35290 (p : Pattern) (ha : d14788 p = 1) (hb : d142666 p = 1) : d168298 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14779 q = 1) (hb : d142666 q = 1) : d168288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14779, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35288 q ha hb
    | true =>
      simp only [d14779, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14780 q = 1) (hb : d142666 q = 1) : d168289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14780, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14780, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14781 q = 1) (hb : d142666 q = 1) : d168290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14781, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14781, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14782 q = 1) (hb : d142666 q = 1) : d168292 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14782, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14782, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14787 q = 1) (hb : d142666 q = 1) : d168297 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14787, d168297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14787, d168297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14788 q = 1) (hb : d142666 q = 1) : d168298 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14788, d168298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14788, d168298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35291 (p : Pattern) (ha : d14794 p = 1) (hb : d142666 p = 1) : d168304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35289 q ha hb
    | true =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d142666 q = 1) : d168301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d142666 q = 1) : d168302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d142666 q = 1) : d168303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14794 q = 1) (hb : d142666 q = 1) : d168304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14794, d168304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14794, d168304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35292 (p : Pattern) (ha : d14798 p = 1) (hb : d142666 p = 1) : d168308 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d142666 q = 1) : d168305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d142666 q = 1) : d168306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d142666 q = 1) : d168307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, d168307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, d168307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14798 q = 1) (hb : d142666 q = 1) : d168308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14798, d168308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14798, d168308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35293 (p : Pattern) (ha : d14804 p = 1) (hb : d142666 p = 1) : d168314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d142666 q = 1) : d168309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35291 q ha hb
    | true =>
      simp only [d14799, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35292 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d142666 q = 1) : d168310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d142666 q = 1) : d168311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d142666 q = 1) : d168312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d142666 q = 1) : d168313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14804 q = 1) (hb : d142666 q = 1) : d168314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14804, d168314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14804, d168314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35294 (p : Pattern) (ha : d14807 p = 1) (hb : d142666 p = 1) : d168317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35289 q ha hb
    | true =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d142666 q = 1) : d168301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d142666 q = 1) : d168302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14793 q = 1) (hb : d142666 q = 1) : d168303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14793, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14793, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14807 q = 1) (hb : d142666 q = 1) : d168317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14807, d168317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14807, d168317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35295 (p : Pattern) (ha : d14808 p = 1) (hb : d142666 p = 1) : d168318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d142666 q = 1) : d168305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d142666 q = 1) : d168306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14797 q = 1) (hb : d142666 q = 1) : d168307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14797, d168307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14797, d168307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14808 q = 1) (hb : d142666 q = 1) : d168318 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14808, d168318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14808, d168318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35296 (p : Pattern) (ha : d14814 p = 1) (hb : d142666 p = 1) : d168324 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14799 q = 1) (hb : d142666 q = 1) : d168309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14799, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35291 q ha hb
    | true =>
      simp only [d14799, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35292 q ha hb
  have h2 (q : Pattern) (ha : d14800 q = 1) (hb : d142666 q = 1) : d168310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14800, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14800, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14801 q = 1) (hb : d142666 q = 1) : d168311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14801, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14801, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14802 q = 1) (hb : d142666 q = 1) : d168312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14802, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14802, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14803 q = 1) (hb : d142666 q = 1) : d168313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14803, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14803, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14809 q = 1) (hb : d142666 q = 1) : d168319 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35294 q ha hb
    | true =>
      simp only [d14809, d168319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35295 q ha hb
  have h7 (q : Pattern) (ha : d14810 q = 1) (hb : d142666 q = 1) : d168320 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, d168320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14811 q = 1) (hb : d142666 q = 1) : d168321 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14811, d168321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14812 q = 1) (hb : d142666 q = 1) : d168322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d168322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14813 q = 1) (hb : d142666 q = 1) : d168323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d168323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14814 q = 1) (hb : d142666 q = 1) : d168324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14814, d168324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14814, d168324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35297 (p : Pattern) (ha : d14855 p = 1) (hb : d142666 p = 1) : d168294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14767 q = 1) (hb : d142666 q = 1) : d168284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35287 q ha hb
    | true =>
      simp only [d14767, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14768 q = 1) (hb : d142666 q = 1) : d168285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14769 q = 1) (hb : d142666 q = 1) : d168286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14773 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14774 q = 1) (hb : d142666 q = 1) : d168288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35288 q ha hb
    | true =>
      simp only [d14774, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d14775 q = 1) (hb : d142666 q = 1) : d168289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14776 q = 1) (hb : d142666 q = 1) : d168290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14777 q = 1) (hb : d142666 q = 1) : d168291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14777, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14853 q = 1) (hb : d142666 q = 1) : d168292 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14853, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14853, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14854 q = 1) (hb : d142666 q = 1) : d168293 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14854, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14854, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d14855 q = 1) (hb : d142666 q = 1) : d168294 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14855, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d14855, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro35298 (p : Pattern) (ha : d14865 p = 1) (hb : d142666 p = 1) : d168304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35297 q ha hb
    | true =>
      simp only [d14856, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d142666 q = 1) : d168301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d142666 q = 1) : d168302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d142666 q = 1) : d168303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14865 q = 1) (hb : d142666 q = 1) : d168304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14865, d168304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14865, d168304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35299 (p : Pattern) (ha : d14965 p = 1) (hb : d142666 p = 1) : d168397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14955 q = 1) (hb : d142666 q = 1) : d168309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14955, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35298 q ha hb
    | true =>
      simp only [d14955, d168309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35292 q ha hb
  have h2 (q : Pattern) (ha : d14956 q = 1) (hb : d142666 q = 1) : d168310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14956, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14956, d168310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14957 q = 1) (hb : d142666 q = 1) : d168311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14957, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14957, d168311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14958 q = 1) (hb : d142666 q = 1) : d168312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14958, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14958, d168312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14959 q = 1) (hb : d142666 q = 1) : d168313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14959, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14959, d168313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14960 q = 1) (hb : d142666 q = 1) : d168392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, d168392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35292 q ha hb
    | true =>
      simp only [d14960, d168392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14961 q = 1) (hb : d142666 q = 1) : d168393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, d168393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, d168393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14962 q = 1) (hb : d142666 q = 1) : d168394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, d168394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14962, d168394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14963 q = 1) (hb : d142666 q = 1) : d168395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, d168395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, d168395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14964 q = 1) (hb : d142666 q = 1) : d168396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, d168396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, d168396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14965 q = 1) (hb : d142666 q = 1) : d168397 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14965, d168397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14965, d168397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35300 (p : Pattern) (ha : d14971 p = 1) (hb : d142666 p = 1) : d168403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14960 q = 1) (hb : d142666 q = 1) : d168392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14960, d168392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35292 q ha hb
    | true =>
      simp only [d14960, d168392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14961 q = 1) (hb : d142666 q = 1) : d168393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14961, d168393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14961, d168393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14962 q = 1) (hb : d142666 q = 1) : d168394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14962, d168394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14962, d168394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14963 q = 1) (hb : d142666 q = 1) : d168395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14963, d168395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14963, d168395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14964 q = 1) (hb : d142666 q = 1) : d168396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14964, d168396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14964, d168396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14966 q = 1) (hb : d142666 q = 1) : d168398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, d168398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35295 q ha hb
    | true =>
      simp only [d14966, d168398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14967 q = 1) (hb : d142666 q = 1) : d168399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, d168399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, d168399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14968 q = 1) (hb : d142666 q = 1) : d168400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, d168400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14968, d168400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d14969 q = 1) (hb : d142666 q = 1) : d168401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, d168401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, d168401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d14970 q = 1) (hb : d142666 q = 1) : d168402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, d168402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, d168402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d14971 q = 1) (hb : d142666 q = 1) : d168403 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14971, d168403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14971, d168403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35301 (p : Pattern) (ha : d14980 p = 1) (hb : d142666 p = 1) : d168412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14966 q = 1) (hb : d142666 q = 1) : d168398 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14966, d168398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35295 q ha hb
    | true =>
      simp only [d14966, d168398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14967 q = 1) (hb : d142666 q = 1) : d168399 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14967, d168399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14967, d168399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14968 q = 1) (hb : d142666 q = 1) : d168400 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14968, d168400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14968, d168400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14969 q = 1) (hb : d142666 q = 1) : d168401 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14969, d168401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14969, d168401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14970 q = 1) (hb : d142666 q = 1) : d168402 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14970, d168402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14970, d168402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14980 q = 1) (hb : d142666 q = 1) : d168412 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d14980, d168412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14980, d168412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35302 (p : Pattern) (ha : d15015 p = 1) (hb : d142665 p = 1) : d168427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15008 q = 1) (hb : d122304 q = 1) : d15008 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15015 q = 1) (hb : d142665 q = 1) : d168427 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15015, d142665, d168427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15015, d142665, d168427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35303 (p : Pattern) (ha : d15048 p = 1) (hb : d142666 p = 1) : d168446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15042 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15043 q = 1) (hb : d142666 q = 1) : d168428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35302 q ha hb
    | true =>
      simp only [d15043, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15044 q = 1) (hb : d142666 q = 1) : d168429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15045 q = 1) (hb : d142666 q = 1) : d168430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15046 q = 1) (hb : d142666 q = 1) : d168436 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15046, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15047 q = 1) (hb : d142666 q = 1) : d168445 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15047, d168445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15047, d168445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15048 q = 1) (hb : d142666 q = 1) : d168446 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15048, d168446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15048, d168446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35304 (p : Pattern) (ha : d15128 p = 1) (hb : d142666 p = 1) : d168469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15049 q = 1) (hb : d142666 q = 1) : d168447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35303 q ha hb
    | true =>
      simp only [d15049, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15050 q = 1) (hb : d142666 q = 1) : d168448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15125 q = 1) (hb : d142666 q = 1) : d168466 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15125, d168466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15125, d168466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15126 q = 1) (hb : d142666 q = 1) : d168467 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15126, d168467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15126, d168467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15127 q = 1) (hb : d142666 q = 1) : d168468 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15127, d168468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15127, d168468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15128 q = 1) (hb : d142666 q = 1) : d168469 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15128, d168469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15128, d168469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35305 (p : Pattern) (ha : d15134 p = 1) (hb : d142666 p = 1) : d168475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15129 q = 1) (hb : d142666 q = 1) : d168470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15129, d168470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35304 q ha hb
    | true =>
      simp only [d15129, d168470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15130 q = 1) (hb : d142666 q = 1) : d168471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15130, d168471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15130, d168471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15131 q = 1) (hb : d142666 q = 1) : d168472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15131, d168472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15131, d168472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15132 q = 1) (hb : d142666 q = 1) : d168473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15132, d168473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15132, d168473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15133 q = 1) (hb : d142666 q = 1) : d168474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15133, d168474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15133, d168474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15134 q = 1) (hb : d142666 q = 1) : d168475 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15134, d168475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15134, d168475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35306 (p : Pattern) (ha : d14819 p = 1) (hb : d142666 p = 1) : d168329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35289 q ha hb
    | true =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d142666 q = 1) : d168301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d142666 q = 1) : d168302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d142666 q = 1) : d168328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, d168328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, d168328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14819 q = 1) (hb : d142666 q = 1) : d168329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14819, d168329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14819, d168329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35307 (p : Pattern) (ha : d14821 p = 1) (hb : d142666 p = 1) : d168331 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d142666 q = 1) : d168305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d142666 q = 1) : d168306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d142666 q = 1) : d168330 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, d168330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, d168330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14821 q = 1) (hb : d142666 q = 1) : d168331 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14821, d168331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14821, d168331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35308 (p : Pattern) (ha : d14828 p = 1) (hb : d142666 p = 1) : d168338 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35289 q ha hb
    | true =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d142666 q = 1) : d168301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d142666 q = 1) : d168336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, d168336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, d168336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d142666 q = 1) : d168337 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, d168337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, d168337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14828 q = 1) (hb : d142666 q = 1) : d168338 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14828, d168338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14828, d168338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35309 (p : Pattern) (ha : d14831 p = 1) (hb : d142666 p = 1) : d168341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d142666 q = 1) : d168305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d142666 q = 1) : d168339 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, d168339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, d168339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d142666 q = 1) : d168340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, d168340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, d168340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14831 q = 1) (hb : d142666 q = 1) : d168341 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14831, d168341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14831, d168341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35310 (p : Pattern) (ha : d14839 p = 1) (hb : d142665 p = 1) : d168345 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14835 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14838 q = 1) (hb : d122304 q = 1) : d14838 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14839 q = 1) (hb : d142665 q = 1) : d168345 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14839, d142665, d168345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14839, d142665, d168345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35311 (p : Pattern) (ha : d14850 p = 1) (hb : d142666 p = 1) : d168351 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14840 q = 1) (hb : d142666 q = 1) : d168346 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14840, d142666, d168346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35310 q ha hb
    | true =>
      simp only [d14840, d142666, d168346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14841 q = 1) (hb : d142666 q = 1) : d168347 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14841, d168347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14841, d168347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14842 q = 1) (hb : d142666 q = 1) : d168348 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14842, d168348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14842, d168348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14844 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14845 q = 1) (hb : d142666 q = 1) : d168284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14845, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35287 q ha hb
    | true =>
      simp only [d14845, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d14846 q = 1) (hb : d142666 q = 1) : d168285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14846, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14846, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14847 q = 1) (hb : d142666 q = 1) : d168286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14847, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14847, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14848 q = 1) (hb : d142666 q = 1) : d168349 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14848, d168349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14848, d168349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14766 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14767 q = 1) (hb : d142666 q = 1) : d168284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35287 q ha hb
    | true =>
      simp only [d14767, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d14768 q = 1) (hb : d142666 q = 1) : d168285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14769 q = 1) (hb : d142666 q = 1) : d168286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d14773 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d14774 q = 1) (hb : d142666 q = 1) : d168288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35288 q ha hb
    | true =>
      simp only [d14774, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d14775 q = 1) (hb : d142666 q = 1) : d168289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14776 q = 1) (hb : d142666 q = 1) : d168290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d14777 q = 1) (hb : d142666 q = 1) : d168291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14777, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14849 q = 1) (hb : d142666 q = 1) : d168350 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14849, d168350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14849, d168350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d14850 q = 1) (hb : d142666 q = 1) : d168351 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14850, d168351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d14850, d168351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro35312 (p : Pattern) (ha : d14861 p = 1) (hb : d142666 p = 1) : d168357 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d142666 q = 1) : d168352 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, d168352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35311 q ha hb
    | true =>
      simp only [d14851, d168352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d142666 q = 1) : d168353 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, d168353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, d168353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35297 q ha hb
    | true =>
      simp only [d14856, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d142666 q = 1) : d168354 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, d168354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, d168354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d142666 q = 1) : d168355 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, d168355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, d168355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d142666 q = 1) : d168356 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, d168356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, d168356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14861 q = 1) (hb : d142666 q = 1) : d168357 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14861, d168357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14861, d168357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35313 (p : Pattern) (ha : d14916 p = 1) (hb : d142666 p = 1) : d168294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14767 q = 1) (hb : d142666 q = 1) : d168284 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14767, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35287 q ha hb
    | true =>
      simp only [d14767, d142666, d168284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d14768 q = 1) (hb : d142666 q = 1) : d168285 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14768, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14768, d168285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14769 q = 1) (hb : d142666 q = 1) : d168286 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14769, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14769, d168286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14773 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d14774 q = 1) (hb : d142666 q = 1) : d168288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14774, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35288 q ha hb
    | true =>
      simp only [d14774, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d14775 q = 1) (hb : d142666 q = 1) : d168289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14775, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14775, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14776 q = 1) (hb : d142666 q = 1) : d168290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14776, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14776, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14777 q = 1) (hb : d142666 q = 1) : d168291 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14777, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14777, d168291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12961 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d14911 q = 1) (hb : d142666 q = 1) : d168288 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d14911, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35288 q ha hb
    | true =>
      simp only [d14911, d142666, d168288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d14912 q = 1) (hb : d142666 q = 1) : d168289 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d14912, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14912, d168289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14913 q = 1) (hb : d142666 q = 1) : d168290 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d14913, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14913, d168290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14914 q = 1) (hb : d142666 q = 1) : d168292 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d14914, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14914, d168292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d14915 q = 1) (hb : d142666 q = 1) : d168293 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d14915, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14915, d168293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d14916 q = 1) (hb : d142666 q = 1) : d168294 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d14916, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d14916, d168294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35314 (p : Pattern) (ha : d14922 p = 1) (hb : d142666 p = 1) : d168363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35313 q ha hb
    | true =>
      simp only [d14917, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d142666 q = 1) : d168360 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, d168360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, d168360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d142666 q = 1) : d168361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, d168361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, d168361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d142666 q = 1) : d168362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, d168362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, d168362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14922 q = 1) (hb : d142666 q = 1) : d168363 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14922, d168363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14922, d168363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35315 (p : Pattern) (ha : d125575 p = 1) (hb : d142666 p = 1) : d168369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d142666 q = 1) : d168332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, d168332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35306 q ha hb
    | true =>
      simp only [d14822, d168332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35307 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d142666 q = 1) : d168333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, d168333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, d168333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d142666 q = 1) : d168334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, d168334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, d168334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d142666 q = 1) : d168335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, d168335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, d168335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d142666 q = 1) : d168342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, d168342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35308 q ha hb
    | true =>
      simp only [d14832, d168342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35309 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d142666 q = 1) : d168343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, d168343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, d168343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d142666 q = 1) : d168344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, d168344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, d168344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d142666 q = 1) : d168358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, d168358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35312 q ha hb
    | true =>
      simp only [d14866, d168358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35298 q ha hb
  have h9 (q : Pattern) (ha : d125571 q = 1) (hb : d142666 q = 1) : d168359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d168359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125571, d168359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d142666 q = 1) : d168364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, d168364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35314 q ha hb
    | true =>
      simp only [d14923, d168364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d142666 q = 1) : d168365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, d168365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, d168365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125572 q = 1) (hb : d142666 q = 1) : d168366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d168366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, d168366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125573 q = 1) (hb : d142666 q = 1) : d168367 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d168367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125573, d168367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125574 q = 1) (hb : d142666 q = 1) : d168368 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d168368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125574, d168368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125575 q = 1) (hb : d142666 q = 1) : d168369 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125575, d168369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125575, d168369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35316 (p : Pattern) (ha : d14929 p = 1) (hb : d142666 p = 1) : d168370 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35289 q ha hb
    | true =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d142666 q = 1) : d168301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14792 q = 1) (hb : d142666 q = 1) : d168302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14792, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14792, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14818 q = 1) (hb : d142666 q = 1) : d168328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14818, d168328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14818, d168328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d14929 q = 1) (hb : d142666 q = 1) : d168370 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14929, d168370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14929, d168370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35317 (p : Pattern) (ha : d14930 p = 1) (hb : d142666 p = 1) : d168371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d142666 q = 1) : d168305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14796 q = 1) (hb : d142666 q = 1) : d168306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14796, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14796, d168306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14820 q = 1) (hb : d142666 q = 1) : d168330 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14820, d168330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14820, d168330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14930 q = 1) (hb : d142666 q = 1) : d168371 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14930, d168371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14930, d168371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35318 (p : Pattern) (ha : d14935 p = 1) (hb : d142666 p = 1) : d168376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14785 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35289 q ha hb
    | true =>
      simp only [d14785, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14786 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14786, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14791 q = 1) (hb : d142666 q = 1) : d168301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14791, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14826 q = 1) (hb : d142666 q = 1) : d168336 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14826, d168336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14826, d168336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14827 q = 1) (hb : d142666 q = 1) : d168337 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14827, d168337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14827, d168337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14935 q = 1) (hb : d142666 q = 1) : d168376 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14935, d168376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14935, d168376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35319 (p : Pattern) (ha : d14936 p = 1) (hb : d142666 p = 1) : d168377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14795 q = 1) (hb : d142666 q = 1) : d168305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14795, d168305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14829 q = 1) (hb : d142666 q = 1) : d168339 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14829, d168339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14829, d168339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14830 q = 1) (hb : d142666 q = 1) : d168340 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14830, d168340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14830, d168340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14936 q = 1) (hb : d142666 q = 1) : d168377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14936, d168377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14936, d168377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35320 (p : Pattern) (ha : d14940 p = 1) (hb : d142666 p = 1) : d168381 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14851 q = 1) (hb : d142666 q = 1) : d168352 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14851, d168352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35311 q ha hb
    | true =>
      simp only [d14851, d168352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14852 q = 1) (hb : d142666 q = 1) : d168353 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14852, d168353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14852, d168353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14856 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35297 q ha hb
    | true =>
      simp only [d14856, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14857 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14858 q = 1) (hb : d142666 q = 1) : d168354 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14858, d168354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14858, d168354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14859 q = 1) (hb : d142666 q = 1) : d168355 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14859, d168355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14859, d168355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14860 q = 1) (hb : d142666 q = 1) : d168356 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14860, d168356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14860, d168356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14940 q = 1) (hb : d142666 q = 1) : d168381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14940, d168381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14940, d168381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35321 (p : Pattern) (ha : d14941 p = 1) (hb : d142666 p = 1) : d168317 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14856 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14856, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35297 q ha hb
    | true =>
      simp only [d14856, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14857 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14857, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14857, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14789 q = 1) (hb : d142666 q = 1) : d168299 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35290 q ha hb
    | true =>
      simp only [d14789, d168299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14790 q = 1) (hb : d142666 q = 1) : d168300 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14790, d168300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14862 q = 1) (hb : d142666 q = 1) : d168301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14862, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14862, d168301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14863 q = 1) (hb : d142666 q = 1) : d168302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14863, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14863, d168302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d14864 q = 1) (hb : d142666 q = 1) : d168303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14864, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14864, d168303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14941 q = 1) (hb : d142666 q = 1) : d168317 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14941, d168317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14941, d168317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35322 (p : Pattern) (ha : d14947 p = 1) (hb : d142666 p = 1) : d168384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14917 q = 1) (hb : d142666 q = 1) : d168295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d14917, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35313 q ha hb
    | true =>
      simp only [d14917, d168295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d14918 q = 1) (hb : d142666 q = 1) : d168296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d14918, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14918, d168296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14919 q = 1) (hb : d142666 q = 1) : d168360 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d14919, d168360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14919, d168360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14920 q = 1) (hb : d142666 q = 1) : d168361 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d14920, d168361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14920, d168361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14921 q = 1) (hb : d142666 q = 1) : d168362 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d14921, d168362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d14921, d168362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14947 q = 1) (hb : d142666 q = 1) : d168384 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d14947, d168384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14947, d168384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35323 (p : Pattern) (ha : d125580 p = 1) (hb : d142666 p = 1) : d168390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14822 q = 1) (hb : d142666 q = 1) : d168332 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14822, d168332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35306 q ha hb
    | true =>
      simp only [d14822, d168332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35307 q ha hb
  have h2 (q : Pattern) (ha : d14823 q = 1) (hb : d142666 q = 1) : d168333 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14823, d168333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14823, d168333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14824 q = 1) (hb : d142666 q = 1) : d168334 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14824, d168334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14824, d168334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14825 q = 1) (hb : d142666 q = 1) : d168335 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14825, d168335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14825, d168335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14832 q = 1) (hb : d142666 q = 1) : d168342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14832, d168342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35308 q ha hb
    | true =>
      simp only [d14832, d168342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35309 q ha hb
  have h6 (q : Pattern) (ha : d14833 q = 1) (hb : d142666 q = 1) : d168343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14833, d168343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14833, d168343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d14834 q = 1) (hb : d142666 q = 1) : d168344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14834, d168344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d14834, d168344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14866 q = 1) (hb : d142666 q = 1) : d168358 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14866, d168358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35312 q ha hb
    | true =>
      simp only [d14866, d168358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35298 q ha hb
  have h9 (q : Pattern) (ha : d125571 q = 1) (hb : d142666 q = 1) : d168359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125571, d168359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125571, d168359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14923 q = 1) (hb : d142666 q = 1) : d168364 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14923, d168364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35314 q ha hb
    | true =>
      simp only [d14923, d168364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d14924 q = 1) (hb : d142666 q = 1) : d168365 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14924, d168365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d14924, d168365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125572 q = 1) (hb : d142666 q = 1) : d168366 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125572, d168366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125572, d168366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125573 q = 1) (hb : d142666 q = 1) : d168367 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125573, d168367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125573, d168367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125574 q = 1) (hb : d142666 q = 1) : d168368 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125574, d168368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125574, d168368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d14931 q = 1) (hb : d142666 q = 1) : d168372 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14931, d168372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35316 q ha hb
    | true =>
      simp only [d14931, d168372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35317 q ha hb
  have h16 (q : Pattern) (ha : d14932 q = 1) (hb : d142666 q = 1) : d168373 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14932, d168373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14932, d168373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14933 q = 1) (hb : d142666 q = 1) : d168374 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14933, d168374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14933, d168374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14934 q = 1) (hb : d142666 q = 1) : d168375 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14934, d168375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14934, d168375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14937 q = 1) (hb : d142666 q = 1) : d168378 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14937, d168378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35318 q ha hb
    | true =>
      simp only [d14937, d168378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35319 q ha hb
  have h20 (q : Pattern) (ha : d14938 q = 1) (hb : d142666 q = 1) : d168379 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14938, d168379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14938, d168379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d14939 q = 1) (hb : d142666 q = 1) : d168380 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14939, d168380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d14939, d168380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d14942 q = 1) (hb : d142666 q = 1) : d168382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, d168382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35320 q ha hb
    | true =>
      simp only [d14942, d168382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35321 q ha hb
  have h23 (q : Pattern) (ha : d125576 q = 1) (hb : d142666 q = 1) : d168383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d168383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125576, d168383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d14948 q = 1) (hb : d142666 q = 1) : d168385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, d168385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35322 q ha hb
    | true =>
      simp only [d14948, d168385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d14949 q = 1) (hb : d142666 q = 1) : d168386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, d168386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d14949, d168386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125577 q = 1) (hb : d142666 q = 1) : d168387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d168387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125577, d168387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125578 q = 1) (hb : d142666 q = 1) : d168388 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125578, d168388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125578, d168388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125579 q = 1) (hb : d142666 q = 1) : d168389 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125579, d168389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125579, d168389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125580 q = 1) (hb : d142666 q = 1) : d168390 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125580, d168390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125580, d168390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro35324 (p : Pattern) (ha : d125587 p = 1) (hb : d142666 p = 1) : d168410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14942 q = 1) (hb : d142666 q = 1) : d168382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14942, d168382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35320 q ha hb
    | true =>
      simp only [d14942, d168382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35321 q ha hb
  have h2 (q : Pattern) (ha : d125576 q = 1) (hb : d142666 q = 1) : d168383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125576, d168383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125576, d168383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14948 q = 1) (hb : d142666 q = 1) : d168385 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14948, d168385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35322 q ha hb
    | true =>
      simp only [d14948, d168385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14949 q = 1) (hb : d142666 q = 1) : d168386 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14949, d168386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14949, d168386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125577 q = 1) (hb : d142666 q = 1) : d168387 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125577, d168387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125577, d168387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125585 q = 1) (hb : d142666 q = 1) : d168408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125585, d168408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125585, d168408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125586 q = 1) (hb : d142666 q = 1) : d168409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125586, d168409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125586, d168409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125587 q = 1) (hb : d142666 q = 1) : d168410 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125587, d168410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125587, d168410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35325 (p : Pattern) (ha : d14992 p = 1) (hb : d142665 p = 1) : d168418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14991 q = 1) (hb : d122304 q = 1) : d14991 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14992 q = 1) (hb : d142665 q = 1) : d168418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14992, d142665, d168418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14992, d142665, d168418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35326 (p : Pattern) (ha : d14999 p = 1) (hb : d142665 p = 1) : d168422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d14993 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14998 q = 1) (hb : d122304 q = 1) : d14998 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14999 q = 1) (hb : d142665 q = 1) : d168422 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14999, d142665, d168422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d14999, d142665, d168422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35327 (p : Pattern) (ha : d15030 p = 1) (hb : d142666 p = 1) : d168433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15000 q = 1) (hb : d142666 q = 1) : d168419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15000, d142666, d168419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35325 q ha hb
    | true =>
      simp only [d15000, d142666, d168419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15001 q = 1) (hb : d142666 q = 1) : d168420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15001, d168420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15001, d168420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15002 q = 1) (hb : d142666 q = 1) : d168421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15002, d168421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15002, d168421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15010 q = 1) (hb : d142666 q = 1) : d168423 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15010, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35326 q ha hb
    | true =>
      simp only [d15010, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15011 q = 1) (hb : d142666 q = 1) : d168424 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15011, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15011, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15012 q = 1) (hb : d142666 q = 1) : d168425 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15012, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15012, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15013 q = 1) (hb : d142666 q = 1) : d168426 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15013, d168426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15013, d168426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15015 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15016 q = 1) (hb : d142666 q = 1) : d168423 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35326 q ha hb
    | true =>
      simp only [d15016, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15017 q = 1) (hb : d142666 q = 1) : d168424 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15018 q = 1) (hb : d142666 q = 1) : d168425 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15024 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15025 q = 1) (hb : d142666 q = 1) : d168428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35302 q ha hb
    | true =>
      simp only [d15025, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d15026 q = 1) (hb : d142666 q = 1) : d168429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15027 q = 1) (hb : d142666 q = 1) : d168430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15028 q = 1) (hb : d142666 q = 1) : d168431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15028, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15029 q = 1) (hb : d142666 q = 1) : d168432 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15029, d168432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15029, d168432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d15030 q = 1) (hb : d142666 q = 1) : d168433 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15030, d168433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15030, d168433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro35328 (p : Pattern) (ha : d15035 p = 1) (hb : d142666 p = 1) : d168438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15015 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15016 q = 1) (hb : d142666 q = 1) : d168423 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35326 q ha hb
    | true =>
      simp only [d15016, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15017 q = 1) (hb : d142666 q = 1) : d168424 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15018 q = 1) (hb : d142666 q = 1) : d168425 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15025 q = 1) (hb : d142666 q = 1) : d168428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35302 q ha hb
    | true =>
      simp only [d15025, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15026 q = 1) (hb : d142666 q = 1) : d168429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15027 q = 1) (hb : d142666 q = 1) : d168430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15028 q = 1) (hb : d142666 q = 1) : d168431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15028, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15033 q = 1) (hb : d142666 q = 1) : d168436 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15033, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15033, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15034 q = 1) (hb : d142666 q = 1) : d168437 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15034, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15034, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15035 q = 1) (hb : d142666 q = 1) : d168438 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15035, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15035, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro35329 (p : Pattern) (ha : d15041 p = 1) (hb : d142666 p = 1) : d168444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15031 q = 1) (hb : d142666 q = 1) : d168434 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15031, d168434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35327 q ha hb
    | true =>
      simp only [d15031, d168434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15032 q = 1) (hb : d142666 q = 1) : d168435 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15032, d168435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15032, d168435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15036 q = 1) (hb : d142666 q = 1) : d168439 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35328 q ha hb
    | true =>
      simp only [d15036, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15037 q = 1) (hb : d142666 q = 1) : d168440 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15038 q = 1) (hb : d142666 q = 1) : d168441 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15038, d168441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15038, d168441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15039 q = 1) (hb : d142666 q = 1) : d168442 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15039, d168442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15039, d168442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15040 q = 1) (hb : d142666 q = 1) : d168443 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15040, d168443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15040, d168443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15041 q = 1) (hb : d142666 q = 1) : d168444 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15041, d168444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15041, d168444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35330 (p : Pattern) (ha : d15054 p = 1) (hb : d142666 p = 1) : d168452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15036 q = 1) (hb : d142666 q = 1) : d168439 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15036, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35328 q ha hb
    | true =>
      simp only [d15036, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15037 q = 1) (hb : d142666 q = 1) : d168440 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15037, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15037, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d142666 q = 1) : d168447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35303 q ha hb
    | true =>
      simp only [d15049, d168447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d142666 q = 1) : d168448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d168448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15051 q = 1) (hb : d142666 q = 1) : d168449 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15051, d168449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15051, d168449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15052 q = 1) (hb : d142666 q = 1) : d168450 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15052, d168450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15052, d168450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15053 q = 1) (hb : d142666 q = 1) : d168451 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15053, d168451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15053, d168451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15054 q = 1) (hb : d142666 q = 1) : d168452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15054, d168452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15054, d168452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35331 (p : Pattern) (ha : d15111 p = 1) (hb : d142666 p = 1) : d168438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15015 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15016 q = 1) (hb : d142666 q = 1) : d168423 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35326 q ha hb
    | true =>
      simp only [d15016, d142666, d168423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15017 q = 1) (hb : d142666 q = 1) : d168424 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d168424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15018 q = 1) (hb : d142666 q = 1) : d168425 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d168425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15024 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15025 q = 1) (hb : d142666 q = 1) : d168428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35302 q ha hb
    | true =>
      simp only [d15025, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15026 q = 1) (hb : d142666 q = 1) : d168429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15027 q = 1) (hb : d142666 q = 1) : d168430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15028 q = 1) (hb : d142666 q = 1) : d168431 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15028, d168431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13190 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15106 q = 1) (hb : d142666 q = 1) : d168428 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15106, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35302 q ha hb
    | true =>
      simp only [d15106, d142666, d168428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15107 q = 1) (hb : d142666 q = 1) : d168429 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15107, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15107, d168429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15108 q = 1) (hb : d142666 q = 1) : d168430 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15108, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15108, d168430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15109 q = 1) (hb : d142666 q = 1) : d168436 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15109, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15109, d168436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15110 q = 1) (hb : d142666 q = 1) : d168437 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15110, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15110, d168437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15111 q = 1) (hb : d142666 q = 1) : d168438 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15111, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15111, d168438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35332 (p : Pattern) (ha : d15117 p = 1) (hb : d142666 p = 1) : d168458 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15112 q = 1) (hb : d142666 q = 1) : d168439 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15112, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35331 q ha hb
    | true =>
      simp only [d15112, d168439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15113 q = 1) (hb : d142666 q = 1) : d168440 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15113, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15113, d168440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15114 q = 1) (hb : d142666 q = 1) : d168455 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15114, d168455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15114, d168455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15115 q = 1) (hb : d142666 q = 1) : d168456 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15115, d168456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15115, d168456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15116 q = 1) (hb : d142666 q = 1) : d168457 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15116, d168457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15116, d168457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15117 q = 1) (hb : d142666 q = 1) : d168458 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15117, d168458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15117, d168458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35333 (p : Pattern) (ha : d125597 p = 1) (hb : d142666 p = 1) : d168464 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15055 q = 1) (hb : d142666 q = 1) : d168453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15055, d168453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35329 q ha hb
    | true =>
      simp only [d15055, d168453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35330 q ha hb
  have h2 (q : Pattern) (ha : d125593 q = 1) (hb : d142666 q = 1) : d168454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125593, d168454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125593, d168454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15118 q = 1) (hb : d142666 q = 1) : d168459 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15118, d168459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35332 q ha hb
    | true =>
      simp only [d15118, d168459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15119 q = 1) (hb : d142666 q = 1) : d168460 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15119, d168460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15119, d168460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125594 q = 1) (hb : d142666 q = 1) : d168461 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125594, d168461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125594, d168461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125595 q = 1) (hb : d142666 q = 1) : d168462 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125595, d168462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125595, d168462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125596 q = 1) (hb : d142666 q = 1) : d168463 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125596, d168463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125596, d168463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125597 q = 1) (hb : d142666 q = 1) : d168464 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125597, d168464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125597, d168464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35334 (p : Pattern) (ha : d125603 p = 1) (hb : d142666 p = 1) : d168481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14805 q = 1) (hb : d142666 q = 1) : d168315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14805, d168315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14805, d168315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35293 q ha hb
  have h2 (q : Pattern) (ha : d14806 q = 1) (hb : d142666 q = 1) : d168316 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14806, d168316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14806, d168316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d14815 q = 1) (hb : d142666 q = 1) : d168325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d168325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35293 q ha hb
    | true =>
      simp only [d14815, d168325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35296 q ha hb
  have h4 (q : Pattern) (ha : d14816 q = 1) (hb : d142666 q = 1) : d168326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d168326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14816, d168326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14817 q = 1) (hb : d142666 q = 1) : d168327 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d14817, d168327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14817, d168327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125581 q = 1) (hb : d142666 q = 1) : d168391 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125581, d168391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35315 q ha hb
    | true =>
      simp only [d125581, d168391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35323 q ha hb
  have h7 (q : Pattern) (ha : d14972 q = 1) (hb : d142666 q = 1) : d168404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14972, d168404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35299 q ha hb
    | true =>
      simp only [d14972, d168404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35300 q ha hb
  have h8 (q : Pattern) (ha : d125582 q = 1) (hb : d142666 q = 1) : d168405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125582, d168405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125582, d168405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125583 q = 1) (hb : d142666 q = 1) : d168406 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125583, d168406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125583, d168406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125584 q = 1) (hb : d142666 q = 1) : d168407 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125584, d168407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125584, d168407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125588 q = 1) (hb : d142666 q = 1) : d168411 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125588, d168411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125588, d168411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35324 q ha hb
  have h12 (q : Pattern) (ha : d14981 q = 1) (hb : d142666 q = 1) : d168413 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14981, d168413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14981, d168413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35301 q ha hb
  have h13 (q : Pattern) (ha : d125589 q = 1) (hb : d142666 q = 1) : d168414 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125589, d168414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125589, d168414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125590 q = 1) (hb : d142666 q = 1) : d168415 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125590, d168415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125590, d168415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125591 q = 1) (hb : d142666 q = 1) : d168416 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125591, d168416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125591, d168416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125592 q = 1) (hb : d142666 q = 1) : d168417 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125592, d168417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125592, d168417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125598 q = 1) (hb : d142666 q = 1) : d168465 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125598, d168465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125598, d168465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35333 q ha hb
  have h18 (q : Pattern) (ha : d15135 q = 1) (hb : d142666 q = 1) : d168476 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15135, d168476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15135, d168476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35305 q ha hb
  have h19 (q : Pattern) (ha : d125599 q = 1) (hb : d142666 q = 1) : d168477 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125599, d168477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125599, d168477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125600 q = 1) (hb : d142666 q = 1) : d168478 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125600, d168478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125600, d168478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125601 q = 1) (hb : d142666 q = 1) : d168479 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125601, d168479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125601, d168479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125602 q = 1) (hb : d142666 q = 1) : d168480 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125602, d168480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125602, d168480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125603 q = 1) (hb : d142666 q = 1) : d168481 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125603, d168481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125603, d168481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35335 (p : Pattern) (ha : d125609 p = 1) (hb : d142666 p = 1) : d168487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125604 q = 1) (hb : d142666 q = 1) : d168482 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125604, d168482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125604, d168482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35334 q ha hb
  have h2 (q : Pattern) (ha : d125605 q = 1) (hb : d142666 q = 1) : d168483 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125605, d168483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125605, d168483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125606 q = 1) (hb : d142666 q = 1) : d168484 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125606, d168484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125606, d168484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125607 q = 1) (hb : d142666 q = 1) : d168485 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125607, d168485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125607, d168485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125608 q = 1) (hb : d142666 q = 1) : d168486 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125608, d168486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125608, d168486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125609 q = 1) (hb : d142666 q = 1) : d168487 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125609, d168487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125609, d168487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35336 (p : Pattern) (ha : d15154 p = 1) (hb : d142665 p = 1) : d168491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15150 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15153 q = 1) (hb : d122304 q = 1) : d15153 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15154 q = 1) (hb : d142665 q = 1) : d168491 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15154, d142665, d168491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15154, d142665, d168491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35337 (p : Pattern) (ha : d15159 p = 1) (hb : d142665 p = 1) : d168495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15155 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15158 q = 1) (hb : d122304 q = 1) : d15158 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15159 q = 1) (hb : d142665 q = 1) : d168495 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15159, d142665, d168495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15159, d142665, d168495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35338 (p : Pattern) (ha : d15177 p = 1) (hb : d142666 p = 1) : d168502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15160 q = 1) (hb : d142666 q = 1) : d168492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35336 q ha hb
    | true =>
      simp only [d15160, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15161 q = 1) (hb : d142666 q = 1) : d168493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15162 q = 1) (hb : d142666 q = 1) : d168494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15166 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15167 q = 1) (hb : d142666 q = 1) : d168496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35337 q ha hb
    | true =>
      simp only [d15167, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15168 q = 1) (hb : d142666 q = 1) : d168497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15169 q = 1) (hb : d142666 q = 1) : d168498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15170 q = 1) (hb : d142666 q = 1) : d168499 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15170, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15171 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15172 q = 1) (hb : d142666 q = 1) : d168496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35337 q ha hb
    | true =>
      simp only [d15172, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15173 q = 1) (hb : d142666 q = 1) : d168497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15174 q = 1) (hb : d142666 q = 1) : d168498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15175 q = 1) (hb : d142666 q = 1) : d168500 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15175, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15176 q = 1) (hb : d142666 q = 1) : d168501 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15176, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15176, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15177 q = 1) (hb : d142666 q = 1) : d168502 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15177, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15177, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35339 (p : Pattern) (ha : d15181 p = 1) (hb : d142666 p = 1) : d168506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15171 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15172 q = 1) (hb : d142666 q = 1) : d168496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35337 q ha hb
    | true =>
      simp only [d15172, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15173 q = 1) (hb : d142666 q = 1) : d168497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15174 q = 1) (hb : d142666 q = 1) : d168498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15175 q = 1) (hb : d142666 q = 1) : d168500 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15175, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15180 q = 1) (hb : d142666 q = 1) : d168505 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15180, d168505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15180, d168505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15181 q = 1) (hb : d142666 q = 1) : d168506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15181, d168506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15181, d168506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35340 (p : Pattern) (ha : d15187 p = 1) (hb : d142666 p = 1) : d168512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35338 q ha hb
    | true =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d142666 q = 1) : d168509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d142666 q = 1) : d168510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d142666 q = 1) : d168511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15187 q = 1) (hb : d142666 q = 1) : d168512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15187, d168512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15187, d168512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35341 (p : Pattern) (ha : d15191 p = 1) (hb : d142666 p = 1) : d168516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d142666 q = 1) : d168513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d142666 q = 1) : d168514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d142666 q = 1) : d168515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, d168515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, d168515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15191 q = 1) (hb : d142666 q = 1) : d168516 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15191, d168516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15191, d168516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35342 (p : Pattern) (ha : d15197 p = 1) (hb : d142666 p = 1) : d168522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d142666 q = 1) : d168517 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35340 q ha hb
    | true =>
      simp only [d15192, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35341 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d142666 q = 1) : d168518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d142666 q = 1) : d168519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d142666 q = 1) : d168520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d142666 q = 1) : d168521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15197 q = 1) (hb : d142666 q = 1) : d168522 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, d168522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, d168522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35343 (p : Pattern) (ha : d15200 p = 1) (hb : d142666 p = 1) : d168525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35338 q ha hb
    | true =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d142666 q = 1) : d168509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d142666 q = 1) : d168510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d142666 q = 1) : d168511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15200 q = 1) (hb : d142666 q = 1) : d168525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15200, d168525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15200, d168525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35344 (p : Pattern) (ha : d15201 p = 1) (hb : d142666 p = 1) : d168526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d142666 q = 1) : d168513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d142666 q = 1) : d168514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d142666 q = 1) : d168515 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, d168515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, d168515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15201 q = 1) (hb : d142666 q = 1) : d168526 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15201, d168526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15201, d168526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35345 (p : Pattern) (ha : d15207 p = 1) (hb : d142666 p = 1) : d168532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d142666 q = 1) : d168517 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35340 q ha hb
    | true =>
      simp only [d15192, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35341 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d142666 q = 1) : d168518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d142666 q = 1) : d168519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d142666 q = 1) : d168520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d142666 q = 1) : d168521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15202 q = 1) (hb : d142666 q = 1) : d168527 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35343 q ha hb
    | true =>
      simp only [d15202, d168527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35344 q ha hb
  have h7 (q : Pattern) (ha : d15203 q = 1) (hb : d142666 q = 1) : d168528 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, d168528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15204 q = 1) (hb : d142666 q = 1) : d168529 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15204, d168529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15205 q = 1) (hb : d142666 q = 1) : d168530 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d168530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15206 q = 1) (hb : d142666 q = 1) : d168531 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d168531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15207 q = 1) (hb : d142666 q = 1) : d168532 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, d168532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15207, d168532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35346 (p : Pattern) (ha : d15248 p = 1) (hb : d142666 p = 1) : d168502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15160 q = 1) (hb : d142666 q = 1) : d168492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35336 q ha hb
    | true =>
      simp only [d15160, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15161 q = 1) (hb : d142666 q = 1) : d168493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15162 q = 1) (hb : d142666 q = 1) : d168494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15166 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15167 q = 1) (hb : d142666 q = 1) : d168496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35337 q ha hb
    | true =>
      simp only [d15167, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15168 q = 1) (hb : d142666 q = 1) : d168497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15169 q = 1) (hb : d142666 q = 1) : d168498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15170 q = 1) (hb : d142666 q = 1) : d168499 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15170, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15246 q = 1) (hb : d142666 q = 1) : d168500 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15246, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15246, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15247 q = 1) (hb : d142666 q = 1) : d168501 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15247, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15247, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15248 q = 1) (hb : d142666 q = 1) : d168502 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15248, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15248, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro35347 (p : Pattern) (ha : d15258 p = 1) (hb : d142666 p = 1) : d168512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35346 q ha hb
    | true =>
      simp only [d15249, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d142666 q = 1) : d168509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d142666 q = 1) : d168510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d142666 q = 1) : d168511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15258 q = 1) (hb : d142666 q = 1) : d168512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15258, d168512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15258, d168512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35348 (p : Pattern) (ha : d15358 p = 1) (hb : d142666 p = 1) : d168605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15348 q = 1) (hb : d142666 q = 1) : d168517 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15348, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35347 q ha hb
    | true =>
      simp only [d15348, d168517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35341 q ha hb
  have h2 (q : Pattern) (ha : d15349 q = 1) (hb : d142666 q = 1) : d168518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15349, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15349, d168518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15350 q = 1) (hb : d142666 q = 1) : d168519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15350, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15350, d168519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15351 q = 1) (hb : d142666 q = 1) : d168520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15351, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15351, d168520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15352 q = 1) (hb : d142666 q = 1) : d168521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15352, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15352, d168521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15353 q = 1) (hb : d142666 q = 1) : d168600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, d168600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35341 q ha hb
    | true =>
      simp only [d15353, d168600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15354 q = 1) (hb : d142666 q = 1) : d168601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, d168601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, d168601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15355 q = 1) (hb : d142666 q = 1) : d168602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, d168602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15355, d168602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15356 q = 1) (hb : d142666 q = 1) : d168603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, d168603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, d168603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15357 q = 1) (hb : d142666 q = 1) : d168604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, d168604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, d168604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15358 q = 1) (hb : d142666 q = 1) : d168605 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15358, d168605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15358, d168605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35349 (p : Pattern) (ha : d15364 p = 1) (hb : d142666 p = 1) : d168611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15353 q = 1) (hb : d142666 q = 1) : d168600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, d168600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35341 q ha hb
    | true =>
      simp only [d15353, d168600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15354 q = 1) (hb : d142666 q = 1) : d168601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, d168601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, d168601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15355 q = 1) (hb : d142666 q = 1) : d168602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, d168602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15355, d168602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15356 q = 1) (hb : d142666 q = 1) : d168603 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, d168603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, d168603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15357 q = 1) (hb : d142666 q = 1) : d168604 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, d168604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, d168604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15359 q = 1) (hb : d142666 q = 1) : d168606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, d168606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35344 q ha hb
    | true =>
      simp only [d15359, d168606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15360 q = 1) (hb : d142666 q = 1) : d168607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, d168607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, d168607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15361 q = 1) (hb : d142666 q = 1) : d168608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, d168608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15361, d168608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15362 q = 1) (hb : d142666 q = 1) : d168609 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, d168609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, d168609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15363 q = 1) (hb : d142666 q = 1) : d168610 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, d168610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, d168610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15364 q = 1) (hb : d142666 q = 1) : d168611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15364, d168611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15364, d168611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35350 (p : Pattern) (ha : d15373 p = 1) (hb : d142666 p = 1) : d168620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15359 q = 1) (hb : d142666 q = 1) : d168606 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, d168606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35344 q ha hb
    | true =>
      simp only [d15359, d168606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15360 q = 1) (hb : d142666 q = 1) : d168607 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, d168607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, d168607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15361 q = 1) (hb : d142666 q = 1) : d168608 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, d168608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15361, d168608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15362 q = 1) (hb : d142666 q = 1) : d168609 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, d168609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, d168609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15363 q = 1) (hb : d142666 q = 1) : d168610 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, d168610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, d168610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15373 q = 1) (hb : d142666 q = 1) : d168620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15373, d168620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15373, d168620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35351 (p : Pattern) (ha : d15408 p = 1) (hb : d142665 p = 1) : d168635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15407 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15401 q = 1) (hb : d122304 q = 1) : d15401 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15408 q = 1) (hb : d142665 q = 1) : d168635 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15408, d142665, d168635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15408, d142665, d168635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35352 (p : Pattern) (ha : d15441 p = 1) (hb : d142666 p = 1) : d168654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15435 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15436 q = 1) (hb : d142666 q = 1) : d168636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35351 q ha hb
    | true =>
      simp only [d15436, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15437 q = 1) (hb : d142666 q = 1) : d168637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15438 q = 1) (hb : d142666 q = 1) : d168638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15439 q = 1) (hb : d142666 q = 1) : d168644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15439, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15440 q = 1) (hb : d142666 q = 1) : d168653 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15440, d168653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15440, d168653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15441 q = 1) (hb : d142666 q = 1) : d168654 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15441, d168654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15441, d168654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35353 (p : Pattern) (ha : d15521 p = 1) (hb : d142666 p = 1) : d168677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15442 q = 1) (hb : d142666 q = 1) : d168655 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35352 q ha hb
    | true =>
      simp only [d15442, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15443 q = 1) (hb : d142666 q = 1) : d168656 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15518 q = 1) (hb : d142666 q = 1) : d168674 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15518, d168674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15518, d168674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15519 q = 1) (hb : d142666 q = 1) : d168675 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15519, d168675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15519, d168675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15520 q = 1) (hb : d142666 q = 1) : d168676 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15520, d168676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15520, d168676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15521 q = 1) (hb : d142666 q = 1) : d168677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15521, d168677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15521, d168677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35354 (p : Pattern) (ha : d15527 p = 1) (hb : d142666 p = 1) : d168683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15522 q = 1) (hb : d142666 q = 1) : d168678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15522, d168678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35353 q ha hb
    | true =>
      simp only [d15522, d168678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15523 q = 1) (hb : d142666 q = 1) : d168679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15523, d168679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15523, d168679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15524 q = 1) (hb : d142666 q = 1) : d168680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15524, d168680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15524, d168680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15525 q = 1) (hb : d142666 q = 1) : d168681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15525, d168681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15525, d168681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15526 q = 1) (hb : d142666 q = 1) : d168682 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15526, d168682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15526, d168682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15527 q = 1) (hb : d142666 q = 1) : d168683 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15527, d168683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15527, d168683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35355 (p : Pattern) (ha : d15212 p = 1) (hb : d142666 p = 1) : d168537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35338 q ha hb
    | true =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d142666 q = 1) : d168509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d142666 q = 1) : d168510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d142666 q = 1) : d168536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, d168536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, d168536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15212 q = 1) (hb : d142666 q = 1) : d168537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15212, d168537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15212, d168537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35356 (p : Pattern) (ha : d15214 p = 1) (hb : d142666 p = 1) : d168539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d142666 q = 1) : d168513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d142666 q = 1) : d168514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d142666 q = 1) : d168538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, d168538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, d168538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15214 q = 1) (hb : d142666 q = 1) : d168539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15214, d168539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15214, d168539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35357 (p : Pattern) (ha : d15221 p = 1) (hb : d142666 p = 1) : d168546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35338 q ha hb
    | true =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d142666 q = 1) : d168509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d142666 q = 1) : d168544 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, d168544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, d168544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d142666 q = 1) : d168545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, d168545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, d168545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15221 q = 1) (hb : d142666 q = 1) : d168546 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15221, d168546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15221, d168546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35358 (p : Pattern) (ha : d15224 p = 1) (hb : d142666 p = 1) : d168549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d142666 q = 1) : d168513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d142666 q = 1) : d168547 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, d168547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, d168547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d142666 q = 1) : d168548 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, d168548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, d168548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15224 q = 1) (hb : d142666 q = 1) : d168549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15224, d168549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15224, d168549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35359 (p : Pattern) (ha : d15232 p = 1) (hb : d142665 p = 1) : d168553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15228 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15231 q = 1) (hb : d122304 q = 1) : d15231 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15232 q = 1) (hb : d142665 q = 1) : d168553 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15232, d142665, d168553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15232, d142665, d168553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35360 (p : Pattern) (ha : d15243 p = 1) (hb : d142666 p = 1) : d168559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15233 q = 1) (hb : d142666 q = 1) : d168554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15233, d142666, d168554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35359 q ha hb
    | true =>
      simp only [d15233, d142666, d168554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15234 q = 1) (hb : d142666 q = 1) : d168555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15234, d168555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15234, d168555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15235 q = 1) (hb : d142666 q = 1) : d168556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15235, d168556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15235, d168556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15237 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15238 q = 1) (hb : d142666 q = 1) : d168492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15238, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35336 q ha hb
    | true =>
      simp only [d15238, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15239 q = 1) (hb : d142666 q = 1) : d168493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15239, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15239, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15240 q = 1) (hb : d142666 q = 1) : d168494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15240, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15240, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15241 q = 1) (hb : d142666 q = 1) : d168557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15241, d168557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15241, d168557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15159 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15160 q = 1) (hb : d142666 q = 1) : d168492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35336 q ha hb
    | true =>
      simp only [d15160, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15161 q = 1) (hb : d142666 q = 1) : d168493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15162 q = 1) (hb : d142666 q = 1) : d168494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15166 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15167 q = 1) (hb : d142666 q = 1) : d168496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35337 q ha hb
    | true =>
      simp only [d15167, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d15168 q = 1) (hb : d142666 q = 1) : d168497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15169 q = 1) (hb : d142666 q = 1) : d168498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15170 q = 1) (hb : d142666 q = 1) : d168499 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15170, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15242 q = 1) (hb : d142666 q = 1) : d168558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15242, d168558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15242, d168558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d15243 q = 1) (hb : d142666 q = 1) : d168559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15243, d168559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15243, d168559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro35361 (p : Pattern) (ha : d15254 p = 1) (hb : d142666 p = 1) : d168565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d142666 q = 1) : d168560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, d168560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35360 q ha hb
    | true =>
      simp only [d15244, d168560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d142666 q = 1) : d168561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, d168561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, d168561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35346 q ha hb
    | true =>
      simp only [d15249, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d142666 q = 1) : d168562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, d168562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, d168562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d142666 q = 1) : d168563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, d168563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, d168563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d142666 q = 1) : d168564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, d168564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, d168564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15254 q = 1) (hb : d142666 q = 1) : d168565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15254, d168565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15254, d168565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35362 (p : Pattern) (ha : d15309 p = 1) (hb : d142666 p = 1) : d168502 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15159 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15160 q = 1) (hb : d142666 q = 1) : d168492 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35336 q ha hb
    | true =>
      simp only [d15160, d142666, d168492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15161 q = 1) (hb : d142666 q = 1) : d168493 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d168493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15162 q = 1) (hb : d142666 q = 1) : d168494 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d168494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15166 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15167 q = 1) (hb : d142666 q = 1) : d168496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35337 q ha hb
    | true =>
      simp only [d15167, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15168 q = 1) (hb : d142666 q = 1) : d168497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15169 q = 1) (hb : d142666 q = 1) : d168498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15170 q = 1) (hb : d142666 q = 1) : d168499 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15170, d168499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13287 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15304 q = 1) (hb : d142666 q = 1) : d168496 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15304, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35337 q ha hb
    | true =>
      simp only [d15304, d142666, d168496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15305 q = 1) (hb : d142666 q = 1) : d168497 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15305, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15305, d168497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15306 q = 1) (hb : d142666 q = 1) : d168498 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15306, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15306, d168498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15307 q = 1) (hb : d142666 q = 1) : d168500 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15307, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15307, d168500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15308 q = 1) (hb : d142666 q = 1) : d168501 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15308, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15308, d168501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15309 q = 1) (hb : d142666 q = 1) : d168502 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15309, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15309, d168502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35363 (p : Pattern) (ha : d15315 p = 1) (hb : d142666 p = 1) : d168571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35362 q ha hb
    | true =>
      simp only [d15310, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d142666 q = 1) : d168568 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, d168568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, d168568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d142666 q = 1) : d168569 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, d168569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, d168569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d142666 q = 1) : d168570 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, d168570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, d168570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15315 q = 1) (hb : d142666 q = 1) : d168571 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15315, d168571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15315, d168571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35364 (p : Pattern) (ha : d125617 p = 1) (hb : d142666 p = 1) : d168577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d142666 q = 1) : d168540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, d168540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35355 q ha hb
    | true =>
      simp only [d15215, d168540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35356 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d142666 q = 1) : d168541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, d168541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, d168541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d142666 q = 1) : d168542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, d168542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, d168542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d142666 q = 1) : d168543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, d168543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, d168543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d142666 q = 1) : d168550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, d168550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35357 q ha hb
    | true =>
      simp only [d15225, d168550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35358 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d142666 q = 1) : d168551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, d168551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, d168551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d142666 q = 1) : d168552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, d168552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, d168552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d142666 q = 1) : d168566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, d168566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35361 q ha hb
    | true =>
      simp only [d15259, d168566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35347 q ha hb
  have h9 (q : Pattern) (ha : d125613 q = 1) (hb : d142666 q = 1) : d168567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d168567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125613, d168567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d142666 q = 1) : d168572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, d168572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35363 q ha hb
    | true =>
      simp only [d15316, d168572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d142666 q = 1) : d168573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, d168573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, d168573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125614 q = 1) (hb : d142666 q = 1) : d168574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d168574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, d168574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125615 q = 1) (hb : d142666 q = 1) : d168575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d168575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125615, d168575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125616 q = 1) (hb : d142666 q = 1) : d168576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d168576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125616, d168576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125617 q = 1) (hb : d142666 q = 1) : d168577 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125617, d168577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125617, d168577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35365 (p : Pattern) (ha : d15322 p = 1) (hb : d142666 p = 1) : d168578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35338 q ha hb
    | true =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d142666 q = 1) : d168509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d142666 q = 1) : d168510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d142666 q = 1) : d168536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, d168536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, d168536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15322 q = 1) (hb : d142666 q = 1) : d168578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15322, d168578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15322, d168578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35366 (p : Pattern) (ha : d15323 p = 1) (hb : d142666 p = 1) : d168579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d142666 q = 1) : d168513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d142666 q = 1) : d168514 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d168514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d142666 q = 1) : d168538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, d168538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, d168538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15323 q = 1) (hb : d142666 q = 1) : d168579 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15323, d168579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15323, d168579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35367 (p : Pattern) (ha : d15328 p = 1) (hb : d142666 p = 1) : d168584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35338 q ha hb
    | true =>
      simp only [d15178, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d142666 q = 1) : d168509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d142666 q = 1) : d168544 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, d168544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, d168544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d142666 q = 1) : d168545 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, d168545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, d168545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15328 q = 1) (hb : d142666 q = 1) : d168584 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15328, d168584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15328, d168584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35368 (p : Pattern) (ha : d15329 p = 1) (hb : d142666 p = 1) : d168585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d142666 q = 1) : d168513 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d168513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d142666 q = 1) : d168547 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, d168547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, d168547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d142666 q = 1) : d168548 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, d168548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, d168548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15329 q = 1) (hb : d142666 q = 1) : d168585 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15329, d168585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15329, d168585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35369 (p : Pattern) (ha : d15333 p = 1) (hb : d142666 p = 1) : d168589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d142666 q = 1) : d168560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, d168560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35360 q ha hb
    | true =>
      simp only [d15244, d168560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d142666 q = 1) : d168561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, d168561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, d168561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35346 q ha hb
    | true =>
      simp only [d15249, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d142666 q = 1) : d168562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, d168562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, d168562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d142666 q = 1) : d168563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, d168563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, d168563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d142666 q = 1) : d168564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, d168564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, d168564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15333 q = 1) (hb : d142666 q = 1) : d168589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15333, d168589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15333, d168589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35370 (p : Pattern) (ha : d15334 p = 1) (hb : d142666 p = 1) : d168525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35346 q ha hb
    | true =>
      simp only [d15249, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d142666 q = 1) : d168507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35339 q ha hb
    | true =>
      simp only [d15182, d168507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d142666 q = 1) : d168508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d168508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d142666 q = 1) : d168509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, d168509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d142666 q = 1) : d168510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, d168510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d142666 q = 1) : d168511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, d168511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15334 q = 1) (hb : d142666 q = 1) : d168525 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15334, d168525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15334, d168525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35371 (p : Pattern) (ha : d15340 p = 1) (hb : d142666 p = 1) : d168592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d142666 q = 1) : d168503 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35362 q ha hb
    | true =>
      simp only [d15310, d168503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d142666 q = 1) : d168504 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, d168504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d142666 q = 1) : d168568 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, d168568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, d168568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d142666 q = 1) : d168569 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, d168569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, d168569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d142666 q = 1) : d168570 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, d168570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, d168570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15340 q = 1) (hb : d142666 q = 1) : d168592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15340, d168592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15340, d168592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35372 (p : Pattern) (ha : d125622 p = 1) (hb : d142666 p = 1) : d168598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d142666 q = 1) : d168540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, d168540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35355 q ha hb
    | true =>
      simp only [d15215, d168540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35356 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d142666 q = 1) : d168541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, d168541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, d168541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d142666 q = 1) : d168542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, d168542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, d168542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d142666 q = 1) : d168543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, d168543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, d168543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d142666 q = 1) : d168550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, d168550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35357 q ha hb
    | true =>
      simp only [d15225, d168550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35358 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d142666 q = 1) : d168551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, d168551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, d168551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d142666 q = 1) : d168552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, d168552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, d168552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d142666 q = 1) : d168566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, d168566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35361 q ha hb
    | true =>
      simp only [d15259, d168566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35347 q ha hb
  have h9 (q : Pattern) (ha : d125613 q = 1) (hb : d142666 q = 1) : d168567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d168567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125613, d168567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d142666 q = 1) : d168572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, d168572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35363 q ha hb
    | true =>
      simp only [d15316, d168572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d142666 q = 1) : d168573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, d168573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, d168573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125614 q = 1) (hb : d142666 q = 1) : d168574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d168574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, d168574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125615 q = 1) (hb : d142666 q = 1) : d168575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d168575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125615, d168575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125616 q = 1) (hb : d142666 q = 1) : d168576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d168576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125616, d168576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15324 q = 1) (hb : d142666 q = 1) : d168580 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15324, d168580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35365 q ha hb
    | true =>
      simp only [d15324, d168580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35366 q ha hb
  have h16 (q : Pattern) (ha : d15325 q = 1) (hb : d142666 q = 1) : d168581 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15325, d168581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15325, d168581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15326 q = 1) (hb : d142666 q = 1) : d168582 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15326, d168582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15326, d168582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15327 q = 1) (hb : d142666 q = 1) : d168583 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15327, d168583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15327, d168583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15330 q = 1) (hb : d142666 q = 1) : d168586 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15330, d168586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35367 q ha hb
    | true =>
      simp only [d15330, d168586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35368 q ha hb
  have h20 (q : Pattern) (ha : d15331 q = 1) (hb : d142666 q = 1) : d168587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15331, d168587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15331, d168587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15332 q = 1) (hb : d142666 q = 1) : d168588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15332, d168588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15332, d168588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15335 q = 1) (hb : d142666 q = 1) : d168590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, d168590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35369 q ha hb
    | true =>
      simp only [d15335, d168590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35370 q ha hb
  have h23 (q : Pattern) (ha : d125618 q = 1) (hb : d142666 q = 1) : d168591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d168591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125618, d168591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15341 q = 1) (hb : d142666 q = 1) : d168593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, d168593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35371 q ha hb
    | true =>
      simp only [d15341, d168593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15342 q = 1) (hb : d142666 q = 1) : d168594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, d168594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15342, d168594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125619 q = 1) (hb : d142666 q = 1) : d168595 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d168595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125619, d168595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125620 q = 1) (hb : d142666 q = 1) : d168596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125620, d168596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125620, d168596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125621 q = 1) (hb : d142666 q = 1) : d168597 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125621, d168597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125621, d168597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125622 q = 1) (hb : d142666 q = 1) : d168598 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125622, d168598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125622, d168598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro35373 (p : Pattern) (ha : d125629 p = 1) (hb : d142666 p = 1) : d168618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15335 q = 1) (hb : d142666 q = 1) : d168590 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, d168590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35369 q ha hb
    | true =>
      simp only [d15335, d168590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35370 q ha hb
  have h2 (q : Pattern) (ha : d125618 q = 1) (hb : d142666 q = 1) : d168591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d168591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125618, d168591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15341 q = 1) (hb : d142666 q = 1) : d168593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, d168593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35371 q ha hb
    | true =>
      simp only [d15341, d168593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15342 q = 1) (hb : d142666 q = 1) : d168594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, d168594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15342, d168594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125619 q = 1) (hb : d142666 q = 1) : d168595 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d168595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125619, d168595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125627 q = 1) (hb : d142666 q = 1) : d168616 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125627, d168616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125627, d168616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125628 q = 1) (hb : d142666 q = 1) : d168617 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125628, d168617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125628, d168617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125629 q = 1) (hb : d142666 q = 1) : d168618 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, d168618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125629, d168618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35374 (p : Pattern) (ha : d15385 p = 1) (hb : d142665 p = 1) : d168626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15379 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15384 q = 1) (hb : d122304 q = 1) : d15384 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15385 q = 1) (hb : d142665 q = 1) : d168626 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15385, d142665, d168626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15385, d142665, d168626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35375 (p : Pattern) (ha : d15392 p = 1) (hb : d142665 p = 1) : d168630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15391 q = 1) (hb : d122304 q = 1) : d15391 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15392 q = 1) (hb : d142665 q = 1) : d168630 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15392, d142665, d168630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15392, d142665, d168630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35376 (p : Pattern) (ha : d15423 p = 1) (hb : d142666 p = 1) : d168641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15393 q = 1) (hb : d142666 q = 1) : d168627 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15393, d142666, d168627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35374 q ha hb
    | true =>
      simp only [d15393, d142666, d168627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15394 q = 1) (hb : d142666 q = 1) : d168628 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15394, d168628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15394, d168628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15395 q = 1) (hb : d142666 q = 1) : d168629 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15395, d168629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15395, d168629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15402 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15403 q = 1) (hb : d142666 q = 1) : d168631 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15403, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35375 q ha hb
    | true =>
      simp only [d15403, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15404 q = 1) (hb : d142666 q = 1) : d168632 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15404, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15404, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15405 q = 1) (hb : d142666 q = 1) : d168633 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15405, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15405, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15406 q = 1) (hb : d142666 q = 1) : d168634 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15406, d168634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15406, d168634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15408 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15409 q = 1) (hb : d142666 q = 1) : d168631 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35375 q ha hb
    | true =>
      simp only [d15409, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15410 q = 1) (hb : d142666 q = 1) : d168632 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15411 q = 1) (hb : d142666 q = 1) : d168633 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15417 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15418 q = 1) (hb : d142666 q = 1) : d168636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35351 q ha hb
    | true =>
      simp only [d15418, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d15419 q = 1) (hb : d142666 q = 1) : d168637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15420 q = 1) (hb : d142666 q = 1) : d168638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15421 q = 1) (hb : d142666 q = 1) : d168639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15421, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15422 q = 1) (hb : d142666 q = 1) : d168640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15422, d168640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15422, d168640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d15423 q = 1) (hb : d142666 q = 1) : d168641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15423, d168641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15423, d168641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro35377 (p : Pattern) (ha : d15428 p = 1) (hb : d142666 p = 1) : d168646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15408 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15409 q = 1) (hb : d142666 q = 1) : d168631 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35375 q ha hb
    | true =>
      simp only [d15409, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15410 q = 1) (hb : d142666 q = 1) : d168632 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15411 q = 1) (hb : d142666 q = 1) : d168633 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15417 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15418 q = 1) (hb : d142666 q = 1) : d168636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35351 q ha hb
    | true =>
      simp only [d15418, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15419 q = 1) (hb : d142666 q = 1) : d168637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15420 q = 1) (hb : d142666 q = 1) : d168638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15421 q = 1) (hb : d142666 q = 1) : d168639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15421, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15426 q = 1) (hb : d142666 q = 1) : d168644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15426, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15426, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15427 q = 1) (hb : d142666 q = 1) : d168645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15427, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15427, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15428 q = 1) (hb : d142666 q = 1) : d168646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15428, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15428, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro35378 (p : Pattern) (ha : d15434 p = 1) (hb : d142666 p = 1) : d168652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15424 q = 1) (hb : d142666 q = 1) : d168642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15424, d168642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35376 q ha hb
    | true =>
      simp only [d15424, d168642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15425 q = 1) (hb : d142666 q = 1) : d168643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15425, d168643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15425, d168643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15429 q = 1) (hb : d142666 q = 1) : d168647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35377 q ha hb
    | true =>
      simp only [d15429, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15430 q = 1) (hb : d142666 q = 1) : d168648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15431 q = 1) (hb : d142666 q = 1) : d168649 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15431, d168649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15431, d168649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15432 q = 1) (hb : d142666 q = 1) : d168650 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15432, d168650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15432, d168650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15433 q = 1) (hb : d142666 q = 1) : d168651 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15433, d168651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15433, d168651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15434 q = 1) (hb : d142666 q = 1) : d168652 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15434, d168652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15434, d168652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35379 (p : Pattern) (ha : d15447 p = 1) (hb : d142666 p = 1) : d168660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15429 q = 1) (hb : d142666 q = 1) : d168647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35377 q ha hb
    | true =>
      simp only [d15429, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15430 q = 1) (hb : d142666 q = 1) : d168648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d142666 q = 1) : d168655 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35352 q ha hb
    | true =>
      simp only [d15442, d168655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d142666 q = 1) : d168656 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d168656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15444 q = 1) (hb : d142666 q = 1) : d168657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15444, d168657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15444, d168657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15445 q = 1) (hb : d142666 q = 1) : d168658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15445, d168658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15445, d168658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15446 q = 1) (hb : d142666 q = 1) : d168659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15446, d168659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15446, d168659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15447 q = 1) (hb : d142666 q = 1) : d168660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15447, d168660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15447, d168660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35380 (p : Pattern) (ha : d15504 p = 1) (hb : d142666 p = 1) : d168646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15408 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15409 q = 1) (hb : d142666 q = 1) : d168631 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35375 q ha hb
    | true =>
      simp only [d15409, d142666, d168631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15410 q = 1) (hb : d142666 q = 1) : d168632 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d168632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15411 q = 1) (hb : d142666 q = 1) : d168633 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d168633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15417 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15418 q = 1) (hb : d142666 q = 1) : d168636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35351 q ha hb
    | true =>
      simp only [d15418, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15419 q = 1) (hb : d142666 q = 1) : d168637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15420 q = 1) (hb : d142666 q = 1) : d168638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15421 q = 1) (hb : d142666 q = 1) : d168639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15421, d168639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13516 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15499 q = 1) (hb : d142666 q = 1) : d168636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15499, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35351 q ha hb
    | true =>
      simp only [d15499, d142666, d168636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15500 q = 1) (hb : d142666 q = 1) : d168637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15500, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15500, d168637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15501 q = 1) (hb : d142666 q = 1) : d168638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15501, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15501, d168638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15502 q = 1) (hb : d142666 q = 1) : d168644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15502, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15502, d168644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15503 q = 1) (hb : d142666 q = 1) : d168645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15503, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15503, d168645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15504 q = 1) (hb : d142666 q = 1) : d168646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15504, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15504, d168646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35381 (p : Pattern) (ha : d15510 p = 1) (hb : d142666 p = 1) : d168666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15505 q = 1) (hb : d142666 q = 1) : d168647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15505, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35380 q ha hb
    | true =>
      simp only [d15505, d168647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15506 q = 1) (hb : d142666 q = 1) : d168648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15506, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15506, d168648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15507 q = 1) (hb : d142666 q = 1) : d168663 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15507, d168663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15507, d168663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15508 q = 1) (hb : d142666 q = 1) : d168664 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15508, d168664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15508, d168664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15509 q = 1) (hb : d142666 q = 1) : d168665 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15509, d168665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15509, d168665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15510 q = 1) (hb : d142666 q = 1) : d168666 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15510, d168666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15510, d168666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35382 (p : Pattern) (ha : d125639 p = 1) (hb : d142666 p = 1) : d168672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15448 q = 1) (hb : d142666 q = 1) : d168661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15448, d168661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35378 q ha hb
    | true =>
      simp only [d15448, d168661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35379 q ha hb
  have h2 (q : Pattern) (ha : d125635 q = 1) (hb : d142666 q = 1) : d168662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, d168662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125635, d168662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15511 q = 1) (hb : d142666 q = 1) : d168667 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15511, d168667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35381 q ha hb
    | true =>
      simp only [d15511, d168667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15512 q = 1) (hb : d142666 q = 1) : d168668 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15512, d168668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15512, d168668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125636 q = 1) (hb : d142666 q = 1) : d168669 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, d168669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125636, d168669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125637 q = 1) (hb : d142666 q = 1) : d168670 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, d168670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125637, d168670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125638 q = 1) (hb : d142666 q = 1) : d168671 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, d168671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125638, d168671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125639 q = 1) (hb : d142666 q = 1) : d168672 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, d168672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125639, d168672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35383 (p : Pattern) (ha : d125645 p = 1) (hb : d142666 p = 1) : d168689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15198 q = 1) (hb : d142666 q = 1) : d168523 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15198, d168523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15198, d168523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35342 q ha hb
  have h2 (q : Pattern) (ha : d15199 q = 1) (hb : d142666 q = 1) : d168524 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15199, d168524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15199, d168524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15208 q = 1) (hb : d142666 q = 1) : d168533 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d168533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35342 q ha hb
    | true =>
      simp only [d15208, d168533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35345 q ha hb
  have h4 (q : Pattern) (ha : d15209 q = 1) (hb : d142666 q = 1) : d168534 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d168534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15209, d168534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15210 q = 1) (hb : d142666 q = 1) : d168535 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15210, d168535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15210, d168535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125623 q = 1) (hb : d142666 q = 1) : d168599 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125623, d168599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35364 q ha hb
    | true =>
      simp only [d125623, d168599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35372 q ha hb
  have h7 (q : Pattern) (ha : d15365 q = 1) (hb : d142666 q = 1) : d168612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15365, d168612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35348 q ha hb
    | true =>
      simp only [d15365, d168612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35349 q ha hb
  have h8 (q : Pattern) (ha : d125624 q = 1) (hb : d142666 q = 1) : d168613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125624, d168613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125624, d168613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125625 q = 1) (hb : d142666 q = 1) : d168614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, d168614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125625, d168614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125626 q = 1) (hb : d142666 q = 1) : d168615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, d168615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125626, d168615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125630 q = 1) (hb : d142666 q = 1) : d168619 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, d168619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125630, d168619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35373 q ha hb
  have h12 (q : Pattern) (ha : d15374 q = 1) (hb : d142666 q = 1) : d168621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15374, d168621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15374, d168621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35350 q ha hb
  have h13 (q : Pattern) (ha : d125631 q = 1) (hb : d142666 q = 1) : d168622 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, d168622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125631, d168622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125632 q = 1) (hb : d142666 q = 1) : d168623 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, d168623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125632, d168623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125633 q = 1) (hb : d142666 q = 1) : d168624 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, d168624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125633, d168624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125634 q = 1) (hb : d142666 q = 1) : d168625 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, d168625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125634, d168625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125640 q = 1) (hb : d142666 q = 1) : d168673 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, d168673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125640, d168673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35382 q ha hb
  have h18 (q : Pattern) (ha : d15528 q = 1) (hb : d142666 q = 1) : d168684 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15528, d168684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15528, d168684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35354 q ha hb
  have h19 (q : Pattern) (ha : d125641 q = 1) (hb : d142666 q = 1) : d168685 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, d168685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125641, d168685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125642 q = 1) (hb : d142666 q = 1) : d168686 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, d168686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125642, d168686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125643 q = 1) (hb : d142666 q = 1) : d168687 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, d168687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125643, d168687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125644 q = 1) (hb : d142666 q = 1) : d168688 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, d168688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125644, d168688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125645 q = 1) (hb : d142666 q = 1) : d168689 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, d168689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125645, d168689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35384 (p : Pattern) (ha : d125651 p = 1) (hb : d142666 p = 1) : d168695 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125646 q = 1) (hb : d142666 q = 1) : d168690 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, d168690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125646, d168690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35383 q ha hb
  have h2 (q : Pattern) (ha : d125647 q = 1) (hb : d142666 q = 1) : d168691 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, d168691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125647, d168691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125648 q = 1) (hb : d142666 q = 1) : d168692 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, d168692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125648, d168692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125649 q = 1) (hb : d142666 q = 1) : d168693 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, d168693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125649, d168693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125650 q = 1) (hb : d142666 q = 1) : d168694 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, d168694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125650, d168694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125651 q = 1) (hb : d142666 q = 1) : d168695 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, d168695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125651, d168695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35385 (p : Pattern) (ha : d15546 p = 1) (hb : d142665 p = 1) : d168700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15545 q = 1) (hb : d122304 q = 1) : d15545 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15546 q = 1) (hb : d142665 q = 1) : d168700 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15546, d142665, d168700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15546, d142665, d168700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35386 (p : Pattern) (ha : d15551 p = 1) (hb : d142665 p = 1) : d168704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15547 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15550 q = 1) (hb : d122304 q = 1) : d15550 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15551 q = 1) (hb : d142665 q = 1) : d168704 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15551, d142665, d168704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15551, d142665, d168704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35387 (p : Pattern) (ha : d15569 p = 1) (hb : d142666 p = 1) : d168711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15552 q = 1) (hb : d142666 q = 1) : d168701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35385 q ha hb
    | true =>
      simp only [d15552, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15553 q = 1) (hb : d142666 q = 1) : d168702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15554 q = 1) (hb : d142666 q = 1) : d168703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15558 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15559 q = 1) (hb : d142666 q = 1) : d168705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35386 q ha hb
    | true =>
      simp only [d15559, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15560 q = 1) (hb : d142666 q = 1) : d168706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15561 q = 1) (hb : d142666 q = 1) : d168707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15562 q = 1) (hb : d142666 q = 1) : d168708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15562, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15563 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15564 q = 1) (hb : d142666 q = 1) : d168705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35386 q ha hb
    | true =>
      simp only [d15564, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15565 q = 1) (hb : d142666 q = 1) : d168706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15566 q = 1) (hb : d142666 q = 1) : d168707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15567 q = 1) (hb : d142666 q = 1) : d168709 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15567, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15568 q = 1) (hb : d142666 q = 1) : d168710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15568, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15568, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15569 q = 1) (hb : d142666 q = 1) : d168711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15569, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15569, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35388 (p : Pattern) (ha : d15573 p = 1) (hb : d142666 p = 1) : d168715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15563 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15564 q = 1) (hb : d142666 q = 1) : d168705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35386 q ha hb
    | true =>
      simp only [d15564, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15565 q = 1) (hb : d142666 q = 1) : d168706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15566 q = 1) (hb : d142666 q = 1) : d168707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15567 q = 1) (hb : d142666 q = 1) : d168709 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15567, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15572 q = 1) (hb : d142666 q = 1) : d168714 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15572, d168714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15572, d168714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15573 q = 1) (hb : d142666 q = 1) : d168715 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15573, d168715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15573, d168715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35389 (p : Pattern) (ha : d15579 p = 1) (hb : d142666 p = 1) : d168721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35387 q ha hb
    | true =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d142666 q = 1) : d168718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d142666 q = 1) : d168719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d142666 q = 1) : d168720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15579 q = 1) (hb : d142666 q = 1) : d168721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15579, d168721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15579, d168721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35390 (p : Pattern) (ha : d15583 p = 1) (hb : d142666 p = 1) : d168725 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d142666 q = 1) : d168722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d142666 q = 1) : d168723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d142666 q = 1) : d168724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, d168724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, d168724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15583 q = 1) (hb : d142666 q = 1) : d168725 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15583, d168725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15583, d168725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35391 (p : Pattern) (ha : d15589 p = 1) (hb : d142666 p = 1) : d168731 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d142666 q = 1) : d168726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35389 q ha hb
    | true =>
      simp only [d15584, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35390 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d142666 q = 1) : d168727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d142666 q = 1) : d168728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d142666 q = 1) : d168729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d142666 q = 1) : d168730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15589 q = 1) (hb : d142666 q = 1) : d168731 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, d168731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, d168731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35392 (p : Pattern) (ha : d15592 p = 1) (hb : d142666 p = 1) : d168734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35387 q ha hb
    | true =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d142666 q = 1) : d168718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d142666 q = 1) : d168719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d142666 q = 1) : d168720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15592 q = 1) (hb : d142666 q = 1) : d168734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15592, d168734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15592, d168734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35393 (p : Pattern) (ha : d15593 p = 1) (hb : d142666 p = 1) : d168735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d142666 q = 1) : d168722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d142666 q = 1) : d168723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d142666 q = 1) : d168724 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, d168724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, d168724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15593 q = 1) (hb : d142666 q = 1) : d168735 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15593, d168735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15593, d168735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35394 (p : Pattern) (ha : d15599 p = 1) (hb : d142666 p = 1) : d168741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d142666 q = 1) : d168726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35389 q ha hb
    | true =>
      simp only [d15584, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35390 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d142666 q = 1) : d168727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d142666 q = 1) : d168728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d142666 q = 1) : d168729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d142666 q = 1) : d168730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15594 q = 1) (hb : d142666 q = 1) : d168736 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35392 q ha hb
    | true =>
      simp only [d15594, d168736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35393 q ha hb
  have h7 (q : Pattern) (ha : d15595 q = 1) (hb : d142666 q = 1) : d168737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, d168737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15596 q = 1) (hb : d142666 q = 1) : d168738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15596, d168738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15597 q = 1) (hb : d142666 q = 1) : d168739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d168739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15598 q = 1) (hb : d142666 q = 1) : d168740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d168740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15599 q = 1) (hb : d142666 q = 1) : d168741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, d168741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15599, d168741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35395 (p : Pattern) (ha : d15636 p = 1) (hb : d142666 p = 1) : d168711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15552 q = 1) (hb : d142666 q = 1) : d168701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35385 q ha hb
    | true =>
      simp only [d15552, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15553 q = 1) (hb : d142666 q = 1) : d168702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15554 q = 1) (hb : d142666 q = 1) : d168703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15558 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15559 q = 1) (hb : d142666 q = 1) : d168705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35386 q ha hb
    | true =>
      simp only [d15559, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15560 q = 1) (hb : d142666 q = 1) : d168706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15561 q = 1) (hb : d142666 q = 1) : d168707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15562 q = 1) (hb : d142666 q = 1) : d168708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15562, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15634 q = 1) (hb : d142666 q = 1) : d168709 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15634, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15634, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15635 q = 1) (hb : d142666 q = 1) : d168710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15635, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15635, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15636 q = 1) (hb : d142666 q = 1) : d168711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15636, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15636, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro35396 (p : Pattern) (ha : d15646 p = 1) (hb : d142666 p = 1) : d168721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35395 q ha hb
    | true =>
      simp only [d15637, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d142666 q = 1) : d168718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d142666 q = 1) : d168719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d142666 q = 1) : d168720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15646 q = 1) (hb : d142666 q = 1) : d168721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15646, d168721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15646, d168721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35397 (p : Pattern) (ha : d15746 p = 1) (hb : d142666 p = 1) : d168810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15736 q = 1) (hb : d142666 q = 1) : d168726 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15736, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35396 q ha hb
    | true =>
      simp only [d15736, d168726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35390 q ha hb
  have h2 (q : Pattern) (ha : d15737 q = 1) (hb : d142666 q = 1) : d168727 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15737, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15737, d168727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15738 q = 1) (hb : d142666 q = 1) : d168728 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15738, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15738, d168728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15739 q = 1) (hb : d142666 q = 1) : d168729 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15739, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15739, d168729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15740 q = 1) (hb : d142666 q = 1) : d168730 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15740, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15740, d168730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15741 q = 1) (hb : d142666 q = 1) : d168805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, d168805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35390 q ha hb
    | true =>
      simp only [d15741, d168805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15742 q = 1) (hb : d142666 q = 1) : d168806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, d168806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, d168806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15743 q = 1) (hb : d142666 q = 1) : d168807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, d168807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15743, d168807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15744 q = 1) (hb : d142666 q = 1) : d168808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, d168808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, d168808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15745 q = 1) (hb : d142666 q = 1) : d168809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, d168809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, d168809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15746 q = 1) (hb : d142666 q = 1) : d168810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15746, d168810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15746, d168810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35398 (p : Pattern) (ha : d15752 p = 1) (hb : d142666 p = 1) : d168816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15741 q = 1) (hb : d142666 q = 1) : d168805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, d168805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35390 q ha hb
    | true =>
      simp only [d15741, d168805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15742 q = 1) (hb : d142666 q = 1) : d168806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, d168806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, d168806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15743 q = 1) (hb : d142666 q = 1) : d168807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, d168807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15743, d168807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15744 q = 1) (hb : d142666 q = 1) : d168808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, d168808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, d168808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15745 q = 1) (hb : d142666 q = 1) : d168809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, d168809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, d168809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15747 q = 1) (hb : d142666 q = 1) : d168811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, d168811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35393 q ha hb
    | true =>
      simp only [d15747, d168811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15748 q = 1) (hb : d142666 q = 1) : d168812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, d168812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, d168812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15749 q = 1) (hb : d142666 q = 1) : d168813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, d168813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15749, d168813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15750 q = 1) (hb : d142666 q = 1) : d168814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, d168814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, d168814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15751 q = 1) (hb : d142666 q = 1) : d168815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, d168815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, d168815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15752 q = 1) (hb : d142666 q = 1) : d168816 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15752, d168816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15752, d168816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35399 (p : Pattern) (ha : d15761 p = 1) (hb : d142666 p = 1) : d168825 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15747 q = 1) (hb : d142666 q = 1) : d168811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, d168811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35393 q ha hb
    | true =>
      simp only [d15747, d168811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15748 q = 1) (hb : d142666 q = 1) : d168812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, d168812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, d168812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15749 q = 1) (hb : d142666 q = 1) : d168813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, d168813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15749, d168813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15750 q = 1) (hb : d142666 q = 1) : d168814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, d168814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, d168814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15751 q = 1) (hb : d142666 q = 1) : d168815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, d168815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, d168815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15761 q = 1) (hb : d142666 q = 1) : d168825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15761, d168825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15761, d168825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35400 (p : Pattern) (ha : d15786 p = 1) (hb : d142665 p = 1) : d168836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15785 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15779 q = 1) (hb : d122304 q = 1) : d15779 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15786 q = 1) (hb : d142665 q = 1) : d168836 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15786, d142665, d168836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15786, d142665, d168836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35401 (p : Pattern) (ha : d15819 p = 1) (hb : d142666 p = 1) : d168855 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15813 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15814 q = 1) (hb : d142666 q = 1) : d168837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35400 q ha hb
    | true =>
      simp only [d15814, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15815 q = 1) (hb : d142666 q = 1) : d168838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15816 q = 1) (hb : d142666 q = 1) : d168839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15817 q = 1) (hb : d142666 q = 1) : d168845 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15817, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15818 q = 1) (hb : d142666 q = 1) : d168854 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15818, d168854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15818, d168854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15819 q = 1) (hb : d142666 q = 1) : d168855 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15819, d168855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15819, d168855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35402 (p : Pattern) (ha : d15899 p = 1) (hb : d142666 p = 1) : d168878 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15820 q = 1) (hb : d142666 q = 1) : d168856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35401 q ha hb
    | true =>
      simp only [d15820, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15821 q = 1) (hb : d142666 q = 1) : d168857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15896 q = 1) (hb : d142666 q = 1) : d168875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15896, d168875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15896, d168875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15897 q = 1) (hb : d142666 q = 1) : d168876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15897, d168876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15897, d168876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15898 q = 1) (hb : d142666 q = 1) : d168877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15898, d168877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15898, d168877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15899 q = 1) (hb : d142666 q = 1) : d168878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15899, d168878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15899, d168878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35403 (p : Pattern) (ha : d15905 p = 1) (hb : d142666 p = 1) : d168884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15900 q = 1) (hb : d142666 q = 1) : d168879 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15900, d168879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35402 q ha hb
    | true =>
      simp only [d15900, d168879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15901 q = 1) (hb : d142666 q = 1) : d168880 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15901, d168880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15901, d168880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15902 q = 1) (hb : d142666 q = 1) : d168881 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15902, d168881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15902, d168881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15903 q = 1) (hb : d142666 q = 1) : d168882 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15903, d168882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15903, d168882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15904 q = 1) (hb : d142666 q = 1) : d168883 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15904, d168883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15904, d168883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15905 q = 1) (hb : d142666 q = 1) : d168884 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15905, d168884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15905, d168884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35404 (p : Pattern) (ha : d15604 p = 1) (hb : d142666 p = 1) : d168746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35387 q ha hb
    | true =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d142666 q = 1) : d168718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d142666 q = 1) : d168719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d142666 q = 1) : d168745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, d168745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, d168745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15604 q = 1) (hb : d142666 q = 1) : d168746 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15604, d168746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15604, d168746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35405 (p : Pattern) (ha : d15606 p = 1) (hb : d142666 p = 1) : d168748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d142666 q = 1) : d168722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d142666 q = 1) : d168723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d142666 q = 1) : d168747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, d168747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, d168747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15606 q = 1) (hb : d142666 q = 1) : d168748 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15606, d168748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15606, d168748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35406 (p : Pattern) (ha : d15613 p = 1) (hb : d142666 p = 1) : d168755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35387 q ha hb
    | true =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d142666 q = 1) : d168718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d142666 q = 1) : d168753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, d168753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, d168753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d142666 q = 1) : d168754 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, d168754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, d168754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15613 q = 1) (hb : d142666 q = 1) : d168755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15613, d168755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15613, d168755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35407 (p : Pattern) (ha : d15616 p = 1) (hb : d142666 p = 1) : d168758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d142666 q = 1) : d168722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d142666 q = 1) : d168756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, d168756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, d168756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d142666 q = 1) : d168757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, d168757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, d168757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15616 q = 1) (hb : d142666 q = 1) : d168758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15616, d168758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15616, d168758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35408 (p : Pattern) (ha : d15621 p = 1) (hb : d142665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15620 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15621 q = 1) (hb : d142665 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15621, d142665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15621, d142665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35409 (p : Pattern) (ha : d15631 p = 1) (hb : d142666 p = 1) : d168764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15546 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15622 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15622, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35408 q ha hb
    | true =>
      simp only [d15622, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15623 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15624 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15625 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15626 q = 1) (hb : d142666 q = 1) : d168701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15626, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35385 q ha hb
    | true =>
      simp only [d15626, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15627 q = 1) (hb : d142666 q = 1) : d168702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15627, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15627, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15628 q = 1) (hb : d142666 q = 1) : d168703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15628, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15628, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15629 q = 1) (hb : d142666 q = 1) : d168762 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15629, d168762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15629, d168762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15551 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15552 q = 1) (hb : d142666 q = 1) : d168701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35385 q ha hb
    | true =>
      simp only [d15552, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15553 q = 1) (hb : d142666 q = 1) : d168702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15554 q = 1) (hb : d142666 q = 1) : d168703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15558 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15559 q = 1) (hb : d142666 q = 1) : d168705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35386 q ha hb
    | true =>
      simp only [d15559, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d15560 q = 1) (hb : d142666 q = 1) : d168706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15561 q = 1) (hb : d142666 q = 1) : d168707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15562 q = 1) (hb : d142666 q = 1) : d168708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15562, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15630 q = 1) (hb : d142666 q = 1) : d168763 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15630, d168763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15630, d168763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d15631 q = 1) (hb : d142666 q = 1) : d168764 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15631, d168764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15631, d168764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro35410 (p : Pattern) (ha : d15642 p = 1) (hb : d142666 p = 1) : d168770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d142666 q = 1) : d168765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, d168765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35409 q ha hb
    | true =>
      simp only [d15632, d168765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d142666 q = 1) : d168766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, d168766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, d168766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35395 q ha hb
    | true =>
      simp only [d15637, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d142666 q = 1) : d168767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, d168767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, d168767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d142666 q = 1) : d168768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, d168768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, d168768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d142666 q = 1) : d168769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, d168769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, d168769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15642 q = 1) (hb : d142666 q = 1) : d168770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15642, d168770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15642, d168770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35411 (p : Pattern) (ha : d15697 p = 1) (hb : d142666 p = 1) : d168711 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15552 q = 1) (hb : d142666 q = 1) : d168701 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35385 q ha hb
    | true =>
      simp only [d15552, d142666, d168701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15553 q = 1) (hb : d142666 q = 1) : d168702 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d168702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15554 q = 1) (hb : d142666 q = 1) : d168703 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d168703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15558 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15559 q = 1) (hb : d142666 q = 1) : d168705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35386 q ha hb
    | true =>
      simp only [d15559, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15560 q = 1) (hb : d142666 q = 1) : d168706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15561 q = 1) (hb : d142666 q = 1) : d168707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15562 q = 1) (hb : d142666 q = 1) : d168708 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15562, d168708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13614 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15692 q = 1) (hb : d142666 q = 1) : d168705 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15692, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35386 q ha hb
    | true =>
      simp only [d15692, d142666, d168705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15693 q = 1) (hb : d142666 q = 1) : d168706 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15693, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15693, d168706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15694 q = 1) (hb : d142666 q = 1) : d168707 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15694, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15694, d168707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15695 q = 1) (hb : d142666 q = 1) : d168709 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15695, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15695, d168709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15696 q = 1) (hb : d142666 q = 1) : d168710 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15696, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15696, d168710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15697 q = 1) (hb : d142666 q = 1) : d168711 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15697, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15697, d168711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35412 (p : Pattern) (ha : d15703 p = 1) (hb : d142666 p = 1) : d168776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35411 q ha hb
    | true =>
      simp only [d15698, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d142666 q = 1) : d168773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, d168773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, d168773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d142666 q = 1) : d168774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, d168774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, d168774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d142666 q = 1) : d168775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, d168775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, d168775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15703 q = 1) (hb : d142666 q = 1) : d168776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15703, d168776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15703, d168776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35413 (p : Pattern) (ha : d125660 p = 1) (hb : d142666 p = 1) : d168782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d142666 q = 1) : d168749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, d168749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35404 q ha hb
    | true =>
      simp only [d15607, d168749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35405 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d142666 q = 1) : d168750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, d168750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, d168750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d142666 q = 1) : d168751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, d168751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, d168751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d142666 q = 1) : d168752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, d168752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, d168752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d142666 q = 1) : d168759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, d168759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35406 q ha hb
    | true =>
      simp only [d15617, d168759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35407 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d142666 q = 1) : d168760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, d168760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, d168760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d142666 q = 1) : d168761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, d168761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, d168761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d142666 q = 1) : d168771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, d168771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35410 q ha hb
    | true =>
      simp only [d15647, d168771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35396 q ha hb
  have h9 (q : Pattern) (ha : d125656 q = 1) (hb : d142666 q = 1) : d168772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d168772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125656, d168772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d142666 q = 1) : d168777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, d168777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35412 q ha hb
    | true =>
      simp only [d15704, d168777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d142666 q = 1) : d168778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, d168778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, d168778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125657 q = 1) (hb : d142666 q = 1) : d168779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d168779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, d168779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125658 q = 1) (hb : d142666 q = 1) : d168780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d168780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125658, d168780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125659 q = 1) (hb : d142666 q = 1) : d168781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d168781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125659, d168781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125660 q = 1) (hb : d142666 q = 1) : d168782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125660, d168782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125660, d168782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35414 (p : Pattern) (ha : d15710 p = 1) (hb : d142666 p = 1) : d168783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35387 q ha hb
    | true =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d142666 q = 1) : d168718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d142666 q = 1) : d168719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d142666 q = 1) : d168745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, d168745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, d168745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15710 q = 1) (hb : d142666 q = 1) : d168783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15710, d168783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15710, d168783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35415 (p : Pattern) (ha : d15711 p = 1) (hb : d142666 p = 1) : d168784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d142666 q = 1) : d168722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d142666 q = 1) : d168723 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d168723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d142666 q = 1) : d168747 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, d168747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, d168747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15711 q = 1) (hb : d142666 q = 1) : d168784 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15711, d168784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15711, d168784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35416 (p : Pattern) (ha : d15716 p = 1) (hb : d142666 p = 1) : d168789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35387 q ha hb
    | true =>
      simp only [d15570, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d142666 q = 1) : d168718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d142666 q = 1) : d168753 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, d168753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, d168753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d142666 q = 1) : d168754 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, d168754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, d168754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15716 q = 1) (hb : d142666 q = 1) : d168789 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15716, d168789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15716, d168789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35417 (p : Pattern) (ha : d15717 p = 1) (hb : d142666 p = 1) : d168790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d142666 q = 1) : d168722 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d168722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d142666 q = 1) : d168756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, d168756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, d168756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d142666 q = 1) : d168757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, d168757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, d168757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15717 q = 1) (hb : d142666 q = 1) : d168790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15717, d168790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15717, d168790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35418 (p : Pattern) (ha : d15721 p = 1) (hb : d142666 p = 1) : d168794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d142666 q = 1) : d168765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, d168765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35409 q ha hb
    | true =>
      simp only [d15632, d168765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d142666 q = 1) : d168766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, d168766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, d168766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35395 q ha hb
    | true =>
      simp only [d15637, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d142666 q = 1) : d168767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, d168767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, d168767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d142666 q = 1) : d168768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, d168768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, d168768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d142666 q = 1) : d168769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, d168769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, d168769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15721 q = 1) (hb : d142666 q = 1) : d168794 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15721, d168794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15721, d168794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35419 (p : Pattern) (ha : d15722 p = 1) (hb : d142666 p = 1) : d168734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35395 q ha hb
    | true =>
      simp only [d15637, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d142666 q = 1) : d168716 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35388 q ha hb
    | true =>
      simp only [d15574, d168716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d142666 q = 1) : d168717 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d168717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d142666 q = 1) : d168718 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, d168718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d142666 q = 1) : d168719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, d168719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d142666 q = 1) : d168720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, d168720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15722 q = 1) (hb : d142666 q = 1) : d168734 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15722, d168734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15722, d168734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35420 (p : Pattern) (ha : d15728 p = 1) (hb : d142666 p = 1) : d168797 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d142666 q = 1) : d168712 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35411 q ha hb
    | true =>
      simp only [d15698, d168712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d142666 q = 1) : d168713 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, d168713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d142666 q = 1) : d168773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, d168773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, d168773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d142666 q = 1) : d168774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, d168774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, d168774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d142666 q = 1) : d168775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, d168775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, d168775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15728 q = 1) (hb : d142666 q = 1) : d168797 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15728, d168797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15728, d168797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35421 (p : Pattern) (ha : d125665 p = 1) (hb : d142666 p = 1) : d168803 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d142666 q = 1) : d168749 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, d168749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35404 q ha hb
    | true =>
      simp only [d15607, d168749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35405 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d142666 q = 1) : d168750 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, d168750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, d168750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d142666 q = 1) : d168751 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, d168751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, d168751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d142666 q = 1) : d168752 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, d168752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, d168752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d142666 q = 1) : d168759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, d168759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35406 q ha hb
    | true =>
      simp only [d15617, d168759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35407 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d142666 q = 1) : d168760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, d168760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, d168760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d142666 q = 1) : d168761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, d168761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, d168761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d142666 q = 1) : d168771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, d168771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35410 q ha hb
    | true =>
      simp only [d15647, d168771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35396 q ha hb
  have h9 (q : Pattern) (ha : d125656 q = 1) (hb : d142666 q = 1) : d168772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d168772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125656, d168772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d142666 q = 1) : d168777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, d168777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35412 q ha hb
    | true =>
      simp only [d15704, d168777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d142666 q = 1) : d168778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, d168778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, d168778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125657 q = 1) (hb : d142666 q = 1) : d168779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d168779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, d168779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125658 q = 1) (hb : d142666 q = 1) : d168780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d168780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125658, d168780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125659 q = 1) (hb : d142666 q = 1) : d168781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d168781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125659, d168781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15712 q = 1) (hb : d142666 q = 1) : d168785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15712, d168785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35414 q ha hb
    | true =>
      simp only [d15712, d168785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35415 q ha hb
  have h16 (q : Pattern) (ha : d15713 q = 1) (hb : d142666 q = 1) : d168786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15713, d168786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15713, d168786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15714 q = 1) (hb : d142666 q = 1) : d168787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15714, d168787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15714, d168787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15715 q = 1) (hb : d142666 q = 1) : d168788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15715, d168788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15715, d168788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15718 q = 1) (hb : d142666 q = 1) : d168791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15718, d168791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35416 q ha hb
    | true =>
      simp only [d15718, d168791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35417 q ha hb
  have h20 (q : Pattern) (ha : d15719 q = 1) (hb : d142666 q = 1) : d168792 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15719, d168792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15719, d168792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15720 q = 1) (hb : d142666 q = 1) : d168793 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15720, d168793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15720, d168793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15723 q = 1) (hb : d142666 q = 1) : d168795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, d168795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35418 q ha hb
    | true =>
      simp only [d15723, d168795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35419 q ha hb
  have h23 (q : Pattern) (ha : d125661 q = 1) (hb : d142666 q = 1) : d168796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d168796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125661, d168796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15729 q = 1) (hb : d142666 q = 1) : d168798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, d168798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35420 q ha hb
    | true =>
      simp only [d15729, d168798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15730 q = 1) (hb : d142666 q = 1) : d168799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, d168799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15730, d168799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125662 q = 1) (hb : d142666 q = 1) : d168800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d168800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125662, d168800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125663 q = 1) (hb : d142666 q = 1) : d168801 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125663, d168801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125663, d168801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125664 q = 1) (hb : d142666 q = 1) : d168802 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125664, d168802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125664, d168802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125665 q = 1) (hb : d142666 q = 1) : d168803 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125665, d168803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125665, d168803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro35422 (p : Pattern) (ha : d125672 p = 1) (hb : d142666 p = 1) : d168823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15723 q = 1) (hb : d142666 q = 1) : d168795 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, d168795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35418 q ha hb
    | true =>
      simp only [d15723, d168795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35419 q ha hb
  have h2 (q : Pattern) (ha : d125661 q = 1) (hb : d142666 q = 1) : d168796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d168796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125661, d168796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15729 q = 1) (hb : d142666 q = 1) : d168798 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, d168798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35420 q ha hb
    | true =>
      simp only [d15729, d168798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15730 q = 1) (hb : d142666 q = 1) : d168799 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, d168799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15730, d168799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125662 q = 1) (hb : d142666 q = 1) : d168800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d168800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125662, d168800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125670 q = 1) (hb : d142666 q = 1) : d168821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125670, d168821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125670, d168821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125671 q = 1) (hb : d142666 q = 1) : d168822 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125671, d168822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125671, d168822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125672 q = 1) (hb : d142666 q = 1) : d168823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, d168823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125672, d168823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35423 (p : Pattern) (ha : d15768 p = 1) (hb : d142665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15767 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d122304 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15768 q = 1) (hb : d142665 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15768, d142665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15768, d142665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35424 (p : Pattern) (ha : d15771 p = 1) (hb : d142665 p = 1) : d168831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d15769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15770 q = 1) (hb : d122304 q = 1) : d15770 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15771 q = 1) (hb : d142665 q = 1) : d168831 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15771, d142665, d168831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d15771, d142665, d168831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro35425 (p : Pattern) (ha : d15801 p = 1) (hb : d142666 p = 1) : d168842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15771 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15772 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15772, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35423 q ha hb
    | true =>
      simp only [d15772, d142666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15773 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15774 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15780 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15781 q = 1) (hb : d142666 q = 1) : d168832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15781, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35424 q ha hb
    | true =>
      simp only [d15781, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15782 q = 1) (hb : d142666 q = 1) : d168833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15782, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15782, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15783 q = 1) (hb : d142666 q = 1) : d168834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15783, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15783, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15784 q = 1) (hb : d142666 q = 1) : d168835 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15784, d168835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15784, d168835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d15786 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15787 q = 1) (hb : d142666 q = 1) : d168832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35424 q ha hb
    | true =>
      simp only [d15787, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15788 q = 1) (hb : d142666 q = 1) : d168833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15789 q = 1) (hb : d142666 q = 1) : d168834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d15795 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d15796 q = 1) (hb : d142666 q = 1) : d168837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35400 q ha hb
    | true =>
      simp only [d15796, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d15797 q = 1) (hb : d142666 q = 1) : d168838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15798 q = 1) (hb : d142666 q = 1) : d168839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d15799 q = 1) (hb : d142666 q = 1) : d168840 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15799, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15800 q = 1) (hb : d142666 q = 1) : d168841 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15800, d168841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15800, d168841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d15801 q = 1) (hb : d142666 q = 1) : d168842 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15801, d168842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d15801, d168842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h20 p ha hb
theorem andIntro35426 (p : Pattern) (ha : d15806 p = 1) (hb : d142666 p = 1) : d168847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15786 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15787 q = 1) (hb : d142666 q = 1) : d168832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35424 q ha hb
    | true =>
      simp only [d15787, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15788 q = 1) (hb : d142666 q = 1) : d168833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15789 q = 1) (hb : d142666 q = 1) : d168834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15795 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15796 q = 1) (hb : d142666 q = 1) : d168837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35400 q ha hb
    | true =>
      simp only [d15796, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15797 q = 1) (hb : d142666 q = 1) : d168838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15798 q = 1) (hb : d142666 q = 1) : d168839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15799 q = 1) (hb : d142666 q = 1) : d168840 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15799, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15804 q = 1) (hb : d142666 q = 1) : d168845 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15804, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15804, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15805 q = 1) (hb : d142666 q = 1) : d168846 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15805, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15805, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15806 q = 1) (hb : d142666 q = 1) : d168847 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15806, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15806, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro35427 (p : Pattern) (ha : d15812 p = 1) (hb : d142666 p = 1) : d168853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15802 q = 1) (hb : d142666 q = 1) : d168843 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15802, d168843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35425 q ha hb
    | true =>
      simp only [d15802, d168843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15803 q = 1) (hb : d142666 q = 1) : d168844 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15803, d168844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15803, d168844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15807 q = 1) (hb : d142666 q = 1) : d168848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35426 q ha hb
    | true =>
      simp only [d15807, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15808 q = 1) (hb : d142666 q = 1) : d168849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15809 q = 1) (hb : d142666 q = 1) : d168850 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15809, d168850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15809, d168850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15810 q = 1) (hb : d142666 q = 1) : d168851 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15810, d168851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15810, d168851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15811 q = 1) (hb : d142666 q = 1) : d168852 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15811, d168852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15811, d168852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15812 q = 1) (hb : d142666 q = 1) : d168853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15812, d168853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15812, d168853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35428 (p : Pattern) (ha : d15825 p = 1) (hb : d142666 p = 1) : d168861 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15807 q = 1) (hb : d142666 q = 1) : d168848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35426 q ha hb
    | true =>
      simp only [d15807, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15808 q = 1) (hb : d142666 q = 1) : d168849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d142666 q = 1) : d168856 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35401 q ha hb
    | true =>
      simp only [d15820, d168856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d142666 q = 1) : d168857 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d168857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15822 q = 1) (hb : d142666 q = 1) : d168858 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15822, d168858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15822, d168858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15823 q = 1) (hb : d142666 q = 1) : d168859 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15823, d168859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15823, d168859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15824 q = 1) (hb : d142666 q = 1) : d168860 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15824, d168860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15824, d168860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15825 q = 1) (hb : d142666 q = 1) : d168861 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15825, d168861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15825, d168861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro35429 (p : Pattern) (ha : d15882 p = 1) (hb : d142666 p = 1) : d168847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15786 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15787 q = 1) (hb : d142666 q = 1) : d168832 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35424 q ha hb
    | true =>
      simp only [d15787, d142666, d168832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15788 q = 1) (hb : d142666 q = 1) : d168833 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d168833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15789 q = 1) (hb : d142666 q = 1) : d168834 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d168834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d15795 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15796 q = 1) (hb : d142666 q = 1) : d168837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35400 q ha hb
    | true =>
      simp only [d15796, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d15797 q = 1) (hb : d142666 q = 1) : d168838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15798 q = 1) (hb : d142666 q = 1) : d168839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15799 q = 1) (hb : d142666 q = 1) : d168840 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15799, d168840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13843 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15877 q = 1) (hb : d142666 q = 1) : d168837 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15877, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35400 q ha hb
    | true =>
      simp only [d15877, d142666, d168837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15878 q = 1) (hb : d142666 q = 1) : d168838 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15878, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15878, d168838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15879 q = 1) (hb : d142666 q = 1) : d168839 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15879, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15879, d168839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15880 q = 1) (hb : d142666 q = 1) : d168845 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15880, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15880, d168845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15881 q = 1) (hb : d142666 q = 1) : d168846 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15881, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15881, d168846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15882 q = 1) (hb : d142666 q = 1) : d168847 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15882, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15882, d168847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro35430 (p : Pattern) (ha : d15888 p = 1) (hb : d142666 p = 1) : d168867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15883 q = 1) (hb : d142666 q = 1) : d168848 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15883, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35429 q ha hb
    | true =>
      simp only [d15883, d168848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15884 q = 1) (hb : d142666 q = 1) : d168849 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15884, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15884, d168849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15885 q = 1) (hb : d142666 q = 1) : d168864 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15885, d168864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15885, d168864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15886 q = 1) (hb : d142666 q = 1) : d168865 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15886, d168865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15886, d168865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15887 q = 1) (hb : d142666 q = 1) : d168866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15887, d168866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15887, d168866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15888 q = 1) (hb : d142666 q = 1) : d168867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15888, d168867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15888, d168867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35431 (p : Pattern) (ha : d125682 p = 1) (hb : d142666 p = 1) : d168873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15826 q = 1) (hb : d142666 q = 1) : d168862 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15826, d168862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35427 q ha hb
    | true =>
      simp only [d15826, d168862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35428 q ha hb
  have h2 (q : Pattern) (ha : d125678 q = 1) (hb : d142666 q = 1) : d168863 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125678, d168863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125678, d168863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15889 q = 1) (hb : d142666 q = 1) : d168868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15889, d168868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35430 q ha hb
    | true =>
      simp only [d15889, d168868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15890 q = 1) (hb : d142666 q = 1) : d168869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15890, d168869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15890, d168869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125679 q = 1) (hb : d142666 q = 1) : d168870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125679, d168870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125679, d168870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125680 q = 1) (hb : d142666 q = 1) : d168871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125680, d168871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125680, d168871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125681 q = 1) (hb : d142666 q = 1) : d168872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125681, d168872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125681, d168872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125682 q = 1) (hb : d142666 q = 1) : d168873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125682, d168873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125682, d168873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35432 (p : Pattern) (ha : d125688 p = 1) (hb : d142666 p = 1) : d168890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15590 q = 1) (hb : d142666 q = 1) : d168732 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15590, d168732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15590, d168732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35391 q ha hb
  have h2 (q : Pattern) (ha : d15591 q = 1) (hb : d142666 q = 1) : d168733 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15591, d168733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15591, d168733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15600 q = 1) (hb : d142666 q = 1) : d168742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d168742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35391 q ha hb
    | true =>
      simp only [d15600, d168742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35394 q ha hb
  have h4 (q : Pattern) (ha : d15601 q = 1) (hb : d142666 q = 1) : d168743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d168743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15601, d168743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15602 q = 1) (hb : d142666 q = 1) : d168744 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15602, d168744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15602, d168744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125666 q = 1) (hb : d142666 q = 1) : d168804 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125666, d168804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35413 q ha hb
    | true =>
      simp only [d125666, d168804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35421 q ha hb
  have h7 (q : Pattern) (ha : d15753 q = 1) (hb : d142666 q = 1) : d168817 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15753, d168817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35397 q ha hb
    | true =>
      simp only [d15753, d168817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35398 q ha hb
  have h8 (q : Pattern) (ha : d125667 q = 1) (hb : d142666 q = 1) : d168818 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125667, d168818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125667, d168818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125668 q = 1) (hb : d142666 q = 1) : d168819 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125668, d168819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125668, d168819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125669 q = 1) (hb : d142666 q = 1) : d168820 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125669, d168820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125669, d168820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125673 q = 1) (hb : d142666 q = 1) : d168824 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125673, d168824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125673, d168824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35422 q ha hb
  have h12 (q : Pattern) (ha : d15762 q = 1) (hb : d142666 q = 1) : d168826 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15762, d168826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15762, d168826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35399 q ha hb
  have h13 (q : Pattern) (ha : d125674 q = 1) (hb : d142666 q = 1) : d168827 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125674, d168827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125674, d168827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125675 q = 1) (hb : d142666 q = 1) : d168828 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125675, d168828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125675, d168828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125676 q = 1) (hb : d142666 q = 1) : d168829 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125676, d168829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125676, d168829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125677 q = 1) (hb : d142666 q = 1) : d168830 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125677, d168830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125677, d168830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125683 q = 1) (hb : d142666 q = 1) : d168874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125683, d168874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125683, d168874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35431 q ha hb
  have h18 (q : Pattern) (ha : d15906 q = 1) (hb : d142666 q = 1) : d168885 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15906, d168885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15906, d168885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35403 q ha hb
  have h19 (q : Pattern) (ha : d125684 q = 1) (hb : d142666 q = 1) : d168886 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125684, d168886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125684, d168886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125685 q = 1) (hb : d142666 q = 1) : d168887 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125685, d168887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125685, d168887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125686 q = 1) (hb : d142666 q = 1) : d168888 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125686, d168888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125686, d168888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125687 q = 1) (hb : d142666 q = 1) : d168889 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125687, d168889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125687, d168889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125688 q = 1) (hb : d142666 q = 1) : d168890 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125688, d168890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125688, d168890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro35433 (p : Pattern) (ha : d125694 p = 1) (hb : d142666 p = 1) : d168896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125689 q = 1) (hb : d142666 q = 1) : d168891 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, d168891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125689, d168891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35432 q ha hb
  have h2 (q : Pattern) (ha : d125690 q = 1) (hb : d142666 q = 1) : d168892 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, d168892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125690, d168892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125691 q = 1) (hb : d142666 q = 1) : d168893 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, d168893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125691, d168893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125692 q = 1) (hb : d142666 q = 1) : d168894 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, d168894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125692, d168894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125693 q = 1) (hb : d142666 q = 1) : d168895 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, d168895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125693, d168895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125694 q = 1) (hb : d142666 q = 1) : d168896 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, d168896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125694, d168896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35434 (p : Pattern) (ha : d125700 p = 1) (hb : d142666 p = 1) : d168902 p = 1 := by
  have h0 (q : Pattern) (ha : d125529 q = 1) (hb : d142666 q = 1) : d168137 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, d168137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35204 q ha hb
    | true =>
      simp only [d125529, d168137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35244 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125569 q = 1) (hb : d142666 q = 1) : d168281 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, d168281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125569, d168281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35286 q ha hb
  have h3 (q : Pattern) (ha : d125570 q = 1) (hb : d142666 q = 1) : d168282 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, d168282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, d168282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125610 q = 1) (hb : d142666 q = 1) : d168488 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, d168488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125610, d168488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35335 q ha hb
  have h5 (q : Pattern) (ha : d125611 q = 1) (hb : d142666 q = 1) : d168489 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, d168489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125611, d168489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125612 q = 1) (hb : d142666 q = 1) : d168490 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, d168490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, d168490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125652 q = 1) (hb : d142666 q = 1) : d168696 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, d168696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125652, d168696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35384 q ha hb
  have h8 (q : Pattern) (ha : d125653 q = 1) (hb : d142666 q = 1) : d168697 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, d168697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125653, d168697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125654 q = 1) (hb : d142666 q = 1) : d168698 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, d168698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125654, d168698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125655 q = 1) (hb : d142666 q = 1) : d168699 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, d168699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, d168699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125695 q = 1) (hb : d142666 q = 1) : d168897 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, d168897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125695, d168897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35433 q ha hb
  have h12 (q : Pattern) (ha : d125696 q = 1) (hb : d142666 q = 1) : d168898 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, d168898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125696, d168898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125697 q = 1) (hb : d142666 q = 1) : d168899 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, d168899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125697, d168899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125698 q = 1) (hb : d142666 q = 1) : d168900 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, d168900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125698, d168900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125699 q = 1) (hb : d142666 q = 1) : d168901 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, d168901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, d168901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125700 q = 1) (hb : d142666 q = 1) : d168902 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, d168902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, d168902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro35435 (p : Pattern) (ha : d125706 p = 1) (hb : d142666 p = 1) : d168908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125701 q = 1) (hb : d142666 q = 1) : d168903 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, d168903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35434 q ha hb
    | true =>
      simp only [d125701, d168903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125702 q = 1) (hb : d142666 q = 1) : d168904 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, d168904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, d168904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125703 q = 1) (hb : d142666 q = 1) : d168905 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, d168905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, d168905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125704 q = 1) (hb : d142666 q = 1) : d168906 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, d168906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, d168906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125705 q = 1) (hb : d142666 q = 1) : d168907 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, d168907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, d168907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125706 q = 1) (hb : d142666 q = 1) : d168908 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, d168908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, d168908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35436 (p : Pattern) (ha : d125712 p = 1) (hb : d142666 p = 1) : d168914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125707 q = 1) (hb : d142666 q = 1) : d168909 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, d168909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35435 q ha hb
    | true =>
      simp only [d125707, d168909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125708 q = 1) (hb : d142666 q = 1) : d168910 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, d168910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, d168910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125709 q = 1) (hb : d142666 q = 1) : d168911 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, d168911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, d168911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125710 q = 1) (hb : d142666 q = 1) : d168912 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, d168912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, d168912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125711 q = 1) (hb : d142666 q = 1) : d168913 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, d168913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, d168913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125712 q = 1) (hb : d142666 q = 1) : d168914 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, d168914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, d168914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35437 (p : Pattern) (ha : d125718 p = 1) (hb : d142666 p = 1) : d168920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125713 q = 1) (hb : d142666 q = 1) : d168915 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, d168915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35436 q ha hb
    | true =>
      simp only [d125713, d168915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125714 q = 1) (hb : d142666 q = 1) : d168916 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, d168916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, d168916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125715 q = 1) (hb : d142666 q = 1) : d168917 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, d168917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, d168917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125716 q = 1) (hb : d142666 q = 1) : d168918 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, d168918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, d168918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125717 q = 1) (hb : d142666 q = 1) : d168919 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, d168919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, d168919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125718 q = 1) (hb : d142666 q = 1) : d168920 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, d168920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, d168920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35438 (p : Pattern) (ha : d125724 p = 1) (hb : d142666 p = 1) : d168926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125719 q = 1) (hb : d142666 q = 1) : d168921 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, d168921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35437 q ha hb
    | true =>
      simp only [d125719, d168921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125720 q = 1) (hb : d142666 q = 1) : d168922 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, d168922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, d168922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125721 q = 1) (hb : d142666 q = 1) : d168923 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, d168923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, d168923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125722 q = 1) (hb : d142666 q = 1) : d168924 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, d168924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, d168924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125723 q = 1) (hb : d142666 q = 1) : d168925 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, d168925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, d168925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125724 q = 1) (hb : d142666 q = 1) : d168926 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, d168926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, d168926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35439 (p : Pattern) (ha : d125730 p = 1) (hb : d142666 p = 1) : d168932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125725 q = 1) (hb : d142666 q = 1) : d168927 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, d168927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35438 q ha hb
    | true =>
      simp only [d125725, d168927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125726 q = 1) (hb : d142666 q = 1) : d168928 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, d168928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, d168928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125727 q = 1) (hb : d142666 q = 1) : d168929 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, d168929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, d168929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125728 q = 1) (hb : d142666 q = 1) : d168930 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, d168930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, d168930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125729 q = 1) (hb : d142666 q = 1) : d168931 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, d168931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, d168931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125730 q = 1) (hb : d142666 q = 1) : d168932 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, d168932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, d168932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35440 (p : Pattern) (ha : d125736 p = 1) (hb : d142666 p = 1) : d168938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125731 q = 1) (hb : d142666 q = 1) : d168933 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, d168933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35439 q ha hb
    | true =>
      simp only [d125731, d168933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125732 q = 1) (hb : d142666 q = 1) : d168934 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, d168934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, d168934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125733 q = 1) (hb : d142666 q = 1) : d168935 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, d168935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, d168935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125734 q = 1) (hb : d142666 q = 1) : d168936 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, d168936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, d168936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125735 q = 1) (hb : d142666 q = 1) : d168937 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, d168937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, d168937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125736 q = 1) (hb : d142666 q = 1) : d168938 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, d168938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, d168938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35441 (p : Pattern) (ha : d125742 p = 1) (hb : d142666 p = 1) : d168944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d142666 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125737 q = 1) (hb : d142666 q = 1) : d168939 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, d168939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35440 q ha hb
    | true =>
      simp only [d125737, d168939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125738 q = 1) (hb : d142666 q = 1) : d168940 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, d168940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, d168940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125739 q = 1) (hb : d142666 q = 1) : d168941 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, d168941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, d168941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125740 q = 1) (hb : d142666 q = 1) : d168942 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, d168942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, d168942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125741 q = 1) (hb : d142666 q = 1) : d168943 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, d168943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, d168943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125742 q = 1) (hb : d142666 q = 1) : d168944 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, d168944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, d168944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35442 (p : Pattern) (ha : d51881 p = 1) (hb : d120066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d51881 q = 1) (hb : d120066 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro35443 (p : Pattern) (ha : d120072 p = 1) (hb : d136862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51881 q = 1) (hb : d120067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35442 q ha hb
    | true =>
      simp only [d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d120068 q = 1) (hb : d136858 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120068, d136858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120068, d136858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d120069 q = 1) (hb : d136859 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120069, d136859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120069, d136859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120070 q = 1) (hb : d136860 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120070, d136860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120070, d136860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120071 q = 1) (hb : d136861 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d120071, d136861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120071, d136861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120072 q = 1) (hb : d136862 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d120072, d136862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120072, d136862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35444 (p : Pattern) (ha : d120078 p = 1) (hb : d136868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d136865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120076 q = 1) (hb : d136866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120076, d136866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120076, d136866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120077 q = 1) (hb : d136867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120077, d136867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120077, d136867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120078 q = 1) (hb : d136868 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120078, d136868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120078, d136868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35445 (p : Pattern) (ha : d120084 p = 1) (hb : d136874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120080 q = 1) (hb : d136870 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120080, d136870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120080, d136870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120081 q = 1) (hb : d136871 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120081, d136871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120081, d136871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120082 q = 1) (hb : d136872 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120082, d136872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120082, d136872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120083 q = 1) (hb : d136873 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120083, d136873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120083, d136873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120084 q = 1) (hb : d136874 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120084, d136874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120084, d136874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35446 (p : Pattern) (ha : d120085 p = 1) (hb : d136875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d136865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120076 q = 1) (hb : d136866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120076, d136866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120076, d136866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120077 q = 1) (hb : d136867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120077, d136867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120077, d136867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120085 q = 1) (hb : d136875 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120085, d136875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120085, d136875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35447 (p : Pattern) (ha : d120091 p = 1) (hb : d136881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120080 q = 1) (hb : d136870 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120080, d136870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120080, d136870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120081 q = 1) (hb : d136871 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120081, d136871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120081, d136871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120082 q = 1) (hb : d136872 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120082, d136872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120082, d136872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120083 q = 1) (hb : d136873 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120083, d136873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120083, d136873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120086 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q ha hb
    | true =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120087 q = 1) (hb : d136877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120087, d136877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120087, d136877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d120088 q = 1) (hb : d136878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120088, d136878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120088, d136878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120089 q = 1) (hb : d136879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120089, d136879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120089, d136879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120090 q = 1) (hb : d136880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120090, d136880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120090, d136880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d120091 q = 1) (hb : d136881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120091, d136881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120091, d136881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35448 (p : Pattern) (ha : d120096 p = 1) (hb : d136886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120086 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q ha hb
    | true =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120087 q = 1) (hb : d136877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120087, d136877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120087, d136877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120088 q = 1) (hb : d136878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120088, d136878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120088, d136878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120089 q = 1) (hb : d136879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120089, d136879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120089, d136879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120090 q = 1) (hb : d136880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120090, d136880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120090, d136880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120096 q = 1) (hb : d136886 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120096, d136886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120096, d136886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35449 (p : Pattern) (ha : d51922 p = 1) (hb : d120102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h3 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d51922 q = 1) (hb : d120102 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h9 p ha hb
theorem andIntro35450 (p : Pattern) (ha : d120108 p = 1) (hb : d136896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51922 q = 1) (hb : d120103 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35449 q ha hb
    | true =>
      simp only [d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d120104 q = 1) (hb : d136892 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120104, d136892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120104, d136892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d120105 q = 1) (hb : d136893 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120105, d136893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120105, d136893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120106 q = 1) (hb : d136894 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120106, d136894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120106, d136894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120107 q = 1) (hb : d136895 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d120107, d136895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120107, d136895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120108 q = 1) (hb : d136896 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d120108, d136896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120108, d136896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro35451 (p : Pattern) (ha : d120114 p = 1) (hb : d136902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120109 q = 1) (hb : d136897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120109, d136897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35450 q ha hb
    | true =>
      simp only [d120109, d136897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120110 q = 1) (hb : d136898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120110, d136898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120110, d136898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120111 q = 1) (hb : d136899 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120111, d136899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120111, d136899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120112 q = 1) (hb : d136900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120112, d136900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120112, d136900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120113 q = 1) (hb : d136901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120113, d136901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120113, d136901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120114 q = 1) (hb : d136902 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120114, d136902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120114, d136902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35452 (p : Pattern) (ha : d120120 p = 1) (hb : d136908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120115 q = 1) (hb : d136903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120115, d136903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35451 q ha hb
    | true =>
      simp only [d120115, d136903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120116 q = 1) (hb : d136904 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120116, d136904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120116, d136904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120117 q = 1) (hb : d136905 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120117, d136905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120117, d136905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120118 q = 1) (hb : d136906 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120118, d136906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120118, d136906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120119 q = 1) (hb : d136907 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120119, d136907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120119, d136907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120120 q = 1) (hb : d136908 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120120, d136908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120120, d136908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35453 (p : Pattern) (ha : d120126 p = 1) (hb : d136914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120092 q = 1) (hb : d136882 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120092, d136882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35445 q ha hb
    | true =>
      simp only [d120092, d136882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35447 q ha hb
  have h2 (q : Pattern) (ha : d120093 q = 1) (hb : d136883 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120093, d136883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120093, d136883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120094 q = 1) (hb : d136884 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120094, d136884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120094, d136884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120095 q = 1) (hb : d136885 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d120095, d136885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120095, d136885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120097 q = 1) (hb : d136887 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120097, d136887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120097, d136887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35448 q ha hb
  have h6 (q : Pattern) (ha : d120098 q = 1) (hb : d136888 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120098, d136888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120098, d136888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120099 q = 1) (hb : d136889 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120099, d136889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120099, d136889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d120100 q = 1) (hb : d136890 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d120100, d136890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120100, d136890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120101 q = 1) (hb : d136891 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d120101, d136891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120101, d136891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120121 q = 1) (hb : d136909 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120121, d136909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120121, d136909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35452 q ha hb
  have h11 (q : Pattern) (ha : d120122 q = 1) (hb : d136910 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120122, d136910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d120122, d136910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d120123 q = 1) (hb : d136911 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120123, d136911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120123, d136911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d120124 q = 1) (hb : d136912 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d120124, d136912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d120124, d136912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d120125 q = 1) (hb : d136913 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d120125, d136913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d120125, d136913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d120126 q = 1) (hb : d136914 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d120126, d136914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d120126, d136914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35454 (p : Pattern) (ha : d120136 p = 1) (hb : d136924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120132 q = 1) (hb : d136920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d136920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120132, d136920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120133 q = 1) (hb : d136921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d136921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120133, d136921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120134 q = 1) (hb : d136922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d136922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120134, d136922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120135 q = 1) (hb : d136923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d136923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d136923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120136 q = 1) (hb : d136924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120136, d136924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120136, d136924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35455 (p : Pattern) (ha : d120143 p = 1) (hb : d136931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120132 q = 1) (hb : d136920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d136920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120132, d136920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120133 q = 1) (hb : d136921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d136921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120133, d136921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120134 q = 1) (hb : d136922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d136922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120134, d136922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120135 q = 1) (hb : d136923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d136923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d136923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120086 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q ha hb
    | true =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120139 q = 1) (hb : d136927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d136927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120139, d136927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120140 q = 1) (hb : d136928 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d136928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120140, d136928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120141 q = 1) (hb : d136929 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d136929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d136929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120142 q = 1) (hb : d136930 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d136930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d136930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d120143 q = 1) (hb : d136931 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120143, d136931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120143, d136931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35456 (p : Pattern) (ha : d120195 p = 1) (hb : d136981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120132 q = 1) (hb : d136920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d136920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120132, d136920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120133 q = 1) (hb : d136921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d136921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120133, d136921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120134 q = 1) (hb : d136922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d136922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120134, d136922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120135 q = 1) (hb : d136923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d136923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d136923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120195 q = 1) (hb : d136981 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120195, d136981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120195, d136981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35457 (p : Pattern) (ha : d120148 p = 1) (hb : d136936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d136865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120076 q = 1) (hb : d136866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120076, d136866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120076, d136866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120147 q = 1) (hb : d136935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120147, d136935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120147, d136935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120148 q = 1) (hb : d136936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120148, d136936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120148, d136936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35458 (p : Pattern) (ha : d120155 p = 1) (hb : d136943 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d136865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120153 q = 1) (hb : d136941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120153, d136941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120153, d136941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120154 q = 1) (hb : d136942 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120154, d136942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120154, d136942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120155 q = 1) (hb : d136943 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120155, d136943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120155, d136943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35459 (p : Pattern) (ha : d9381 p = 1) (hb : d51989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18 q ha hb
    | true =>
      simp only [d133, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d134 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d135, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5448 q = 1) (hb : d51987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5448, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5449 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5449, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21, d51873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d22 q = 1) (hb : d51874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22, d51874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d23 q = 1) (hb : d51875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23, d51875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9381 q = 1) (hb : d51989 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d51989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9381, d51989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro35460 (p : Pattern) (ha : d51994 p = 1) (hb : d167946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35459 q ha hb
    | true =>
      simp only [d9382, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9384 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12493 q = 1) (hb : d51992 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12493, d51992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12494 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12494, d51993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14078 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14078, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14078, d51994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51994 q = 1) (hb : d167946 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d167946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35461 (p : Pattern) (ha : d136951 p = 1) (hb : d167952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51994 q = 1) (hb : d167947 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d167947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35460 q ha hb
    | true =>
      simp only [d167947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d136947 q = 1) (hb : d167948 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136947, d167948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136947, d167948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d136948 q = 1) (hb : d167949 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136948, d167949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136948, d167949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51881 q = 1) (hb : d120067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35442 q ha hb
    | true =>
      simp only [d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d120068 q = 1) (hb : d136858 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120068, d136858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120068, d136858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d120069 q = 1) (hb : d136859 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120069, d136859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120069, d136859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136949 q = 1) (hb : d167950 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136949, d167950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136949, d167950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d120070 q = 1) (hb : d136860 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120070, d136860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120070, d136860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d136950 q = 1) (hb : d167951 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136950, d167951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d136950, d167951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d136951 q = 1) (hb : d167952 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136951, d167952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136951, d167952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35462 (p : Pattern) (ha : d136957 p = 1) (hb : d167958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d167955 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d136955 q = 1) (hb : d167956 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136955, d167956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136955, d167956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136956 q = 1) (hb : d167957 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136956, d167957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136956, d167957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136957 q = 1) (hb : d167958 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136957, d167958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136957, d167958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35463 (p : Pattern) (ha : d136963 p = 1) (hb : d167964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120149 q = 1) (hb : d136937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120149, d136937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35457 q ha hb
    | true =>
      simp only [d120149, d136937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120150 q = 1) (hb : d136938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120150, d136938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120150, d136938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120151 q = 1) (hb : d136939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120151, d136939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120151, d136939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120152 q = 1) (hb : d136940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120152, d136940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120152, d136940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120156 q = 1) (hb : d136944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120156, d136944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35458 q ha hb
    | true =>
      simp only [d120156, d136944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120157 q = 1) (hb : d136945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120157, d136945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120157, d136945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120158 q = 1) (hb : d136946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120158, d136946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120158, d136946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d136958 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
    | true =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d136959 q = 1) (hb : d167960 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136959, d167960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136959, d167960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d120080 q = 1) (hb : d136870 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120080, d136870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120080, d136870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d136960 q = 1) (hb : d167961 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136960, d167961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d136960, d167961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d136961 q = 1) (hb : d167962 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136961, d167962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d136961, d167962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d136962 q = 1) (hb : d167963 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136962, d167963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d136962, d167963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d136963 q = 1) (hb : d167964 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136963, d167964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136963, d167964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro35464 (p : Pattern) (ha : d120178 p = 1) (hb : d136964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d136865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120076 q = 1) (hb : d136866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120076, d136866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120076, d136866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120147 q = 1) (hb : d136935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120147, d136935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120147, d136935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120178 q = 1) (hb : d136964 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120178, d136964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120178, d136964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35465 (p : Pattern) (ha : d120183 p = 1) (hb : d136969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120075 q = 1) (hb : d136865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120075, d136865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120153 q = 1) (hb : d136941 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d120153, d136941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120153, d136941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120154 q = 1) (hb : d136942 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d120154, d136942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120154, d136942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120183 q = 1) (hb : d136969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d120183, d136969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d120183, d136969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro35466 (p : Pattern) (ha : d136973 p = 1) (hb : d167965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d167955 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d136955 q = 1) (hb : d167956 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136955, d167956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136955, d167956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d136956 q = 1) (hb : d167957 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d136956, d167957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136956, d167957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d136973 q = 1) (hb : d167965 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d136973, d167965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d136973, d167965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35467 (p : Pattern) (ha : d136979 p = 1) (hb : d167971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120149 q = 1) (hb : d136937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120149, d136937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35457 q ha hb
    | true =>
      simp only [d120149, d136937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120150 q = 1) (hb : d136938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120150, d136938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120150, d136938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120151 q = 1) (hb : d136939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120151, d136939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120151, d136939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120152 q = 1) (hb : d136940 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120152, d136940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120152, d136940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120156 q = 1) (hb : d136944 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120156, d136944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35458 q ha hb
    | true =>
      simp only [d120156, d136944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d120157 q = 1) (hb : d136945 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120157, d136945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120157, d136945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d120158 q = 1) (hb : d136946 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120158, d136946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d120158, d136946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d136958 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
    | true =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d136959 q = 1) (hb : d167960 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136959, d167960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136959, d167960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d120080 q = 1) (hb : d136870 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120080, d136870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d120080, d136870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d136960 q = 1) (hb : d167961 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136960, d167961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d136960, d167961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d136961 q = 1) (hb : d167962 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136961, d167962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d136961, d167962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d136962 q = 1) (hb : d167963 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136962, d167963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d136962, d167963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d120179 q = 1) (hb : d136965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120179, d136965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35464 q ha hb
    | true =>
      simp only [d120179, d136965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d120180 q = 1) (hb : d136966 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120180, d136966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120180, d136966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d120181 q = 1) (hb : d136967 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120181, d136967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d120181, d136967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d120182 q = 1) (hb : d136968 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120182, d136968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120182, d136968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d120184 q = 1) (hb : d136970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120184, d136970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35465 q ha hb
    | true =>
      simp only [d120184, d136970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d120185 q = 1) (hb : d136971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120185, d136971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120185, d136971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d120186 q = 1) (hb : d136972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120186, d136972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d120186, d136972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d136974 q = 1) (hb : d167966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35466 q ha hb
    | true =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d136975 q = 1) (hb : d167967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136975, d167967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d136975, d167967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d120086 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q ha hb
    | true =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d120087 q = 1) (hb : d136877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120087, d136877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d120087, d136877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d136976 q = 1) (hb : d167968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136976, d167968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d136976, d167968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d136977 q = 1) (hb : d167969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136977, d167969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d136977, d167969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d136978 q = 1) (hb : d167970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136978, d167970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d136978, d167970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d136979 q = 1) (hb : d167971 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136979, d167971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d136979, d167971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro35468 (p : Pattern) (ha : d136988 p = 1) (hb : d167978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136974 q = 1) (hb : d167966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35466 q ha hb
    | true =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d136975 q = 1) (hb : d167967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d136975, d167967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d136975, d167967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d120086 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q ha hb
    | true =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120087 q = 1) (hb : d136877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120087, d136877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120087, d136877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d136976 q = 1) (hb : d167968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d136976, d167968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d136976, d167968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d136986 q = 1) (hb : d167976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d136986, d167976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136986, d167976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d136987 q = 1) (hb : d167977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d136987, d167977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136987, d167977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136988 q = 1) (hb : d167978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d136988, d167978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136988, d167978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35469 (p : Pattern) (ha : d52048 p = 1) (hb : d167984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12599 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12599, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35459 q ha hb
  have h3 (q : Pattern) (ha : d9382 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35459 q ha hb
    | true =>
      simp only [d9382, d51990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12600 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12600, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9384 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9384, d51991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12601 q = 1) (hb : d52046 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12601, d52046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12602 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12602, d52047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14155 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14155, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14155, d52048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52048 q = 1) (hb : d167984 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d167984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35470 (p : Pattern) (ha : d136998 p = 1) (hb : d167990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52048 q = 1) (hb : d167985 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d167985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35469 q ha hb
    | true =>
      simp only [d167985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d136994 q = 1) (hb : d167986 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136994, d167986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136994, d167986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d136995 q = 1) (hb : d167987 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136995, d167987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136995, d167987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51922 q = 1) (hb : d120103 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35449 q ha hb
    | true =>
      simp only [d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d120104 q = 1) (hb : d136892 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120104, d136892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120104, d136892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d120105 q = 1) (hb : d136893 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120105, d136893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120105, d136893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d136996 q = 1) (hb : d167988 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136996, d167988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d136996, d167988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d120106 q = 1) (hb : d136894 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d120106, d136894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d120106, d136894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d136997 q = 1) (hb : d167989 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d136997, d167989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d136997, d167989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d136998 q = 1) (hb : d167990 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d136998, d167990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136998, d167990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro35471 (p : Pattern) (ha : d137004 p = 1) (hb : d167996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136999 q = 1) (hb : d167991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136999, d167991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35470 q ha hb
    | true =>
      simp only [d136999, d167991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137000 q = 1) (hb : d167992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137000, d167992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137000, d167992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120109 q = 1) (hb : d136897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120109, d136897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35450 q ha hb
    | true =>
      simp only [d120109, d136897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120110 q = 1) (hb : d136898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120110, d136898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120110, d136898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137001 q = 1) (hb : d167993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137001, d167993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137001, d167993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137002 q = 1) (hb : d167994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137002, d167994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137002, d167994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137003 q = 1) (hb : d167995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137003, d167995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137003, d167995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137004 q = 1) (hb : d167996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137004, d167996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137004, d167996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35472 (p : Pattern) (ha : d137010 p = 1) (hb : d168002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137005 q = 1) (hb : d167997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137005, d167997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35471 q ha hb
    | true =>
      simp only [d137005, d167997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35451 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136903 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d137006 q = 1) (hb : d167998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137006, d167998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d137006, d167998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d120115 q = 1) (hb : d136903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120115, d136903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35451 q ha hb
    | true =>
      simp only [d120115, d136903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120116 q = 1) (hb : d136904 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120116, d136904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d120116, d136904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d137007 q = 1) (hb : d167999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137007, d167999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137007, d167999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d137008 q = 1) (hb : d168000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137008, d168000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137008, d168000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137009 q = 1) (hb : d168001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137009, d168001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137009, d168001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137010 q = 1) (hb : d168002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137010, d168002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137010, d168002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35473 (p : Pattern) (ha : d137016 p = 1) (hb : d168008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120137 q = 1) (hb : d136925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120137, d136925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120137, d136925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35454 q ha hb
  have h2 (q : Pattern) (ha : d120138 q = 1) (hb : d136926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120138, d136926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d120138, d136926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d120144 q = 1) (hb : d136932 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120144, d136932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35454 q ha hb
    | true =>
      simp only [d120144, d136932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35455 q ha hb
  have h4 (q : Pattern) (ha : d120145 q = 1) (hb : d136933 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d120145, d136933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d120145, d136933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120146 q = 1) (hb : d136934 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d120146, d136934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120146, d136934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136980 q = 1) (hb : d167972 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136980, d167972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35463 q ha hb
    | true =>
      simp only [d136980, d167972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35467 q ha hb
  have h7 (q : Pattern) (ha : d120196 q = 1) (hb : d136982 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d120196, d136982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35456 q ha hb
    | true =>
      simp only [d120196, d136982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d136983 q = 1) (hb : d167973 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136983, d167973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d136983, d167973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d136984 q = 1) (hb : d167974 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136984, d167974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136984, d167974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d136985 q = 1) (hb : d167975 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136985, d167975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d136985, d167975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d136989 q = 1) (hb : d167979 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d136989, d167979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136989, d167979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35468 q ha hb
  have h12 (q : Pattern) (ha : d136990 q = 1) (hb : d167980 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d136990, d167980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d136990, d167980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d136991 q = 1) (hb : d167981 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d136991, d167981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d136991, d167981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d136992 q = 1) (hb : d167982 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d136992, d167982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d136992, d167982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d136993 q = 1) (hb : d167983 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d136993, d167983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d136993, d167983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137011 q = 1) (hb : d168003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d137011, d168003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137011, d168003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35472 q ha hb
  have h17 (q : Pattern) (ha : d137012 q = 1) (hb : d168004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d137012, d168004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d137012, d168004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d137013 q = 1) (hb : d168005 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d137013, d168005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137013, d168005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137014 q = 1) (hb : d168006 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d137014, d168006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d137014, d168006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d137015 q = 1) (hb : d168007 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d137015, d168007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d137015, d168007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d137016 q = 1) (hb : d168008 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d137016, d168008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d137016, d168008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro35474 (p : Pattern) (ha : d137022 p = 1) (hb : d168014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120127 q = 1) (hb : d136915 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d120127, d136915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120127, d136915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35453 q ha hb
  have h2 (q : Pattern) (ha : d120128 q = 1) (hb : d136916 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d120128, d136916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120128, d136916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120129 q = 1) (hb : d136917 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d120129, d136917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120129, d136917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d120130 q = 1) (hb : d136918 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d120130, d136918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120130, d136918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120131 q = 1) (hb : d136919 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d120131, d136919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120131, d136919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137017 q = 1) (hb : d168009 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d137017, d168009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137017, d168009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35473 q ha hb
  have h7 (q : Pattern) (ha : d137018 q = 1) (hb : d168010 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d137018, d168010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137018, d168010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137019 q = 1) (hb : d168011 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d137019, d168011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137019, d168011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d137020 q = 1) (hb : d168012 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d137020, d168012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137020, d168012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137021 q = 1) (hb : d168013 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d137021, d168013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137021, d168013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137022 q = 1) (hb : d168014 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d137022, d168014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d137022, d168014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35475 (p : Pattern) (ha : d120334 p = 1) (hb : d137102 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120086 q = 1) (hb : d136876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q ha hb
    | true =>
      simp only [d120086, d136876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120139 q = 1) (hb : d136927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120139, d136927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120139, d136927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120140 q = 1) (hb : d136928 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120140, d136928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120140, d136928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120141 q = 1) (hb : d136929 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120141, d136929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120141, d136929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120142 q = 1) (hb : d136930 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120142, d136930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120142, d136930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120334 q = 1) (hb : d137102 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120334, d137102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120334, d137102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35476 (p : Pattern) (ha : d120378 p = 1) (hb : d137136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120115 q = 1) (hb : d136903 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120115, d136903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35451 q ha hb
    | true =>
      simp only [d120115, d136903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d120374 q = 1) (hb : d137132 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120374, d137132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120374, d137132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120375 q = 1) (hb : d137133 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120375, d137133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d120375, d137133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120376 q = 1) (hb : d137134 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120376, d137134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120376, d137134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d120377 q = 1) (hb : d137135 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120377, d137135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120377, d137135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120378 q = 1) (hb : d137136 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d120378, d137136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120378, d137136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35477 (p : Pattern) (ha : d137027 p = 1) (hb : d168019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136958 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
    | true =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q hb ha
  have h2 (q : Pattern) (ha : d137023 q = 1) (hb : d168015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137023, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137023, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137024 q = 1) (hb : d168016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137024, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137024, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137025 q = 1) (hb : d168017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137025, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137025, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137026 q = 1) (hb : d168018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137026, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137026, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d137027 q = 1) (hb : d168019 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137027, d168019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137027, d168019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35478 (p : Pattern) (ha : d137034 p = 1) (hb : d168026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136958 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
    | true =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q hb ha
  have h2 (q : Pattern) (ha : d137023 q = 1) (hb : d168015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137023, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137023, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137024 q = 1) (hb : d168016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137024, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137024, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137025 q = 1) (hb : d168017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137025, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137025, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137026 q = 1) (hb : d168018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137026, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137026, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d136974 q = 1) (hb : d167966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35466 q ha hb
    | true =>
      simp only [d136974, d167966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35446 q hb ha
  have h7 (q : Pattern) (ha : d137030 q = 1) (hb : d168022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137030, d168022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137030, d168022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137031 q = 1) (hb : d168023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137031, d168023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137031, d168023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d137032 q = 1) (hb : d168024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137032, d168024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137032, d168024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d137033 q = 1) (hb : d168025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137033, d168025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137033, d168025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137034 q = 1) (hb : d168026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137034, d168026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137034, d168026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35479 (p : Pattern) (ha : d137093 p = 1) (hb : d168087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136958 q = 1) (hb : d167959 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
    | true =>
      simp only [d136958, d167959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q hb ha
  have h2 (q : Pattern) (ha : d137023 q = 1) (hb : d168015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137023, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137023, d168015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137024 q = 1) (hb : d168016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137024, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137024, d168016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137025 q = 1) (hb : d168017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137025, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137025, d168017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137026 q = 1) (hb : d168018 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d137026, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137026, d168018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120079 q = 1) (hb : d136869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35444 q ha hb
    | true =>
      simp only [d120079, d136869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d120132 q = 1) (hb : d136920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d120132, d136920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120132, d136920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d120133 q = 1) (hb : d136921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d120133, d136921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d120133, d136921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d120134 q = 1) (hb : d136922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120134, d136922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120134, d136922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d120135 q = 1) (hb : d136923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d120135, d136923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120135, d136923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d137093 q = 1) (hb : d168087 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d137093, d168087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137093, d168087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro35480 (p : Pattern) (ha : d137039 p = 1) (hb : d168031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d167955 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d136955 q = 1) (hb : d167956 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136955, d167956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136955, d167956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137038 q = 1) (hb : d168030 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137038, d168030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137038, d168030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137039 q = 1) (hb : d168031 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137039, d168031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137039, d168031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35481 (p : Pattern) (ha : d137046 p = 1) (hb : d168038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d167955 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137044 q = 1) (hb : d168036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137044, d168036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137044, d168036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137045 q = 1) (hb : d168037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137045, d168037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137045, d168037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137046 q = 1) (hb : d168038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137046, d168038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137046, d168038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35482 (p : Pattern) (ha : d137066 p = 1) (hb : d168060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137063 q = 1) (hb : d168057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137063, d168057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137063, d168057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137064 q = 1) (hb : d168058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137064, d168058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137064, d168058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137065 q = 1) (hb : d168059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137065, d168059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137065, d168059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137066 q = 1) (hb : d168060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137066, d168060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137066, d168060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro35483 (p : Pattern) (ha : d5011 p = 1) (hb : d51983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128 q = 1) (hb : d51979 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128, d51979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14 q = 1) (hb : d51866 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14, d51866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129 q = 1) (hb : d51980 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129, d51980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d534 q = 1) (hb : d51981 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d534, d51981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d534, d51981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15 q = 1) (hb : d51867 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15, d51867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16 q = 1) (hb : d51868 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16, d51868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5010 q = 1) (hb : d51982 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d5010, d51982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5010, d51982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17 q = 1) (hb : d51869 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d17, d51869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17, d51869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5011 q = 1) (hb : d51983 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d5011, d51983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5011, d51983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro35484 (p : Pattern) (ha : d9467 p = 1) (hb : d52117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d52112 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41 q ha hb
    | true =>
      simp only [d313, d52112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d314 q = 1) (hb : d52113 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d52113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9452 q = 1) (hb : d51984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35483 q ha hb
    | true =>
      simp only [d9452, d51984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9453 q = 1) (hb : d51985 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9453, d51985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9464 q = 1) (hb : d52114 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9464, d52114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9464, d52114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9465 q = 1) (hb : d52115 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9465, d52115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9465, d52115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9466 q = 1) (hb : d52116 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9466, d52116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9466, d52116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9454 q = 1) (hb : d51986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9454, d51986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d51873 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d9455 q = 1) (hb : d51987 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9455, d51987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9456 q = 1) (hb : d51988 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9456, d51988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9467 q = 1) (hb : d52117 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9467, d52117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9467, d52117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro35485 (p : Pattern) (ha : d52122 p = 1) (hb : d168042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35484 q ha hb
    | true =>
      simp only [d9468, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9470 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12748 q = 1) (hb : d52120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12748, d52120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12749 q = 1) (hb : d52121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12749, d52121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51993 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14262 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14262, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14262, d52122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52122 q = 1) (hb : d168042 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35486 (p : Pattern) (ha : d112929 p = 1) (hb : d167946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12493 q = 1) (hb : d112927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12493, d112927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12494 q = 1) (hb : d112928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12494, d112928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14078 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14078, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14078, d112929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112929 q = 1) (hb : d167946 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d167946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro35487 (p : Pattern) (ha : d167243 p = 1) (hb : d168048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52122 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52122 q = 1) (hb : d168043 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35485 q ha hb
    | true =>
      simp only [d168043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137050 q = 1) (hb : d168044 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137050, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137050, d168044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137051 q = 1) (hb : d168045 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137051, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137051, d168045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112929 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d112929 q = 1) (hb : d167947 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d167947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35486 q ha hb
    | true =>
      simp only [d167947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167239 q = 1) (hb : d167948 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167239, d167948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167239, d167948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167240 q = 1) (hb : d167949 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167240, d167949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167240, d167949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167241 q = 1) (hb : d168046 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167241, d168046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167241, d168046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51994 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51994 q = 1) (hb : d167947 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d167947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35460 q ha hb
    | true =>
      simp only [d167947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d136947 q = 1) (hb : d167948 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136947, d167948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136947, d167948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d136948 q = 1) (hb : d167949 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136948, d167949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136948, d167949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d51881 q = 1) (hb : d120067 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35442 q ha hb
    | true =>
      simp only [d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d120068 q = 1) (hb : d136858 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120068, d136858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120068, d136858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d120069 q = 1) (hb : d136859 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120069, d136859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120069, d136859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d136949 q = 1) (hb : d167950 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136949, d167950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d136949, d167950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d167242 q = 1) (hb : d168047 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167242, d168047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167242, d168047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167243 q = 1) (hb : d168048 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167243, d168048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167243, d168048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro35488 (p : Pattern) (ha : d167249 p = 1) (hb : d168054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167244 q = 1) (hb : d168049 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167244, d168049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35487 q ha hb
    | true =>
      simp only [d167244, d168049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167245 q = 1) (hb : d168050 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167245, d168050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167245, d168050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167246 q = 1) (hb : d168051 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167246, d168051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167246, d168051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167247 q = 1) (hb : d168052 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167247, d168052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167247, d168052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167248 q = 1) (hb : d168053 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167248, d168053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167248, d168053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167249 q = 1) (hb : d168054 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167249, d168054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167249, d168054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro35489 (p : Pattern) (ha : d167255 p = 1) (hb : d168066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137040 q = 1) (hb : d168032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137040, d168032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35480 q ha hb
    | true =>
      simp only [d137040, d168032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35457 q hb ha
  have h2 (q : Pattern) (ha : d137041 q = 1) (hb : d168033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137041, d168033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137041, d168033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137042 q = 1) (hb : d168034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137042, d168034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137042, d168034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137043 q = 1) (hb : d168035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137043, d168035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137043, d168035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137047 q = 1) (hb : d168039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137047, d168039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35481 q ha hb
    | true =>
      simp only [d137047, d168039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35458 q hb ha
  have h6 (q : Pattern) (ha : d137048 q = 1) (hb : d168040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137048, d168040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137048, d168040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137049 q = 1) (hb : d168041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137049, d168041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137049, d168041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167250 q = 1) (hb : d168055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167250, d168055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35488 q ha hb
    | true =>
      simp only [d167250, d168055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136958 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167251 q = 1) (hb : d168056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167251, d168056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167251, d168056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137067 q = 1) (hb : d168061 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137067, d168061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35482 q ha hb
    | true =>
      simp only [d137067, d168061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137068 q = 1) (hb : d168062 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137068, d168062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137068, d168062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167252 q = 1) (hb : d168063 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167252, d168063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167252, d168063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167253 q = 1) (hb : d168064 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167253, d168064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167253, d168064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167254 q = 1) (hb : d168065 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167254, d168065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167254, d168065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d167255 q = 1) (hb : d168066 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167255, d168066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167255, d168066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro35490 (p : Pattern) (ha : d137073 p = 1) (hb : d168067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d167955 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d136955 q = 1) (hb : d167956 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d136955, d167956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136955, d167956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d137038 q = 1) (hb : d168030 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137038, d168030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137038, d168030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d137073 q = 1) (hb : d168067 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137073, d168067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137073, d168067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35491 (p : Pattern) (ha : d137078 p = 1) (hb : d168072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d120073 q = 1) (hb : d136863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35443 q ha hb
    | true =>
      simp only [d120073, d136863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120074 q = 1) (hb : d136864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120074, d136864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d136954 q = 1) (hb : d167955 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d136954, d167955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d137044 q = 1) (hb : d168036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137044, d168036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137044, d168036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137045 q = 1) (hb : d168037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137045, d168037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137045, d168037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d137078 q = 1) (hb : d168072 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137078, d168072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137078, d168072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35492 (p : Pattern) (ha : d137085 p = 1) (hb : d168079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137063 q = 1) (hb : d168057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137063, d168057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137063, d168057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137064 q = 1) (hb : d168058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137064, d168058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137064, d168058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137065 q = 1) (hb : d168059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137065, d168059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137065, d168059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137085 q = 1) (hb : d168079 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137085, d168079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137085, d168079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35493 (p : Pattern) (ha : d167256 p = 1) (hb : d168076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167244 q = 1) (hb : d168049 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d167244, d168049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35487 q ha hb
    | true =>
      simp only [d167244, d168049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d167245 q = 1) (hb : d168050 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d167245, d168050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167245, d168050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d136952 q = 1) (hb : d167953 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35461 q ha hb
    | true =>
      simp only [d136952, d167953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d136953 q = 1) (hb : d167954 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136953, d167954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d167246 q = 1) (hb : d168051 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d167246, d168051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d167246, d168051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d167247 q = 1) (hb : d168052 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d167247, d168052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d167247, d168052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d167248 q = 1) (hb : d168053 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d167248, d168053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d167248, d168053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167256 q = 1) (hb : d168076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d167256, d168076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167256, d168076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro35494 (p : Pattern) (ha : d167262 p = 1) (hb : d168085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d137040 q = 1) (hb : d168032 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137040, d168032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35480 q ha hb
    | true =>
      simp only [d137040, d168032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35457 q hb ha
  have h2 (q : Pattern) (ha : d137041 q = 1) (hb : d168033 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137041, d168033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137041, d168033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137042 q = 1) (hb : d168034 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137042, d168034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137042, d168034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137043 q = 1) (hb : d168035 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137043, d168035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137043, d168035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d137047 q = 1) (hb : d168039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137047, d168039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35481 q ha hb
    | true =>
      simp only [d137047, d168039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35458 q hb ha
  have h6 (q : Pattern) (ha : d137048 q = 1) (hb : d168040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137048, d168040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137048, d168040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d137049 q = 1) (hb : d168041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137049, d168041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d137049, d168041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d167250 q = 1) (hb : d168055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167250, d168055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35488 q ha hb
    | true =>
      simp only [d167250, d168055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35462 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d136958 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d167251 q = 1) (hb : d168056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167251, d168056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d167251, d168056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d137067 q = 1) (hb : d168061 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137067, d168061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35482 q ha hb
    | true =>
      simp only [d137067, d168061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d137068 q = 1) (hb : d168062 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137068, d168062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d137068, d168062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d167252 q = 1) (hb : d168063 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167252, d168063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d167252, d168063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d167253 q = 1) (hb : d168064 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167253, d168064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d167253, d168064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d167254 q = 1) (hb : d168065 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167254, d168065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167254, d168065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d137074 q = 1) (hb : d168068 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137074, d168068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35490 q ha hb
    | true =>
      simp only [d137074, d168068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35464 q hb ha
  have h17 (q : Pattern) (ha : d137075 q = 1) (hb : d168069 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137075, d168069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137075, d168069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d137076 q = 1) (hb : d168070 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137076, d168070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d137076, d168070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d137077 q = 1) (hb : d168071 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d137077, d168071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137077, d168071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d137079 q = 1) (hb : d168073 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137079, d168073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35491 q ha hb
    | true =>
      simp only [d137079, d168073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35465 q hb ha
  have h21 (q : Pattern) (ha : d137080 q = 1) (hb : d168074 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137080, d168074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137080, d168074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d137081 q = 1) (hb : d168075 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d137081, d168075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d137081, d168075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d167257 q = 1) (hb : d168077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167257, d168077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35493 q ha hb
    | true =>
      simp only [d167257, d168077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35466 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d136974 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d167258 q = 1) (hb : d168078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167258, d168078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d167258, d168078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d137086 q = 1) (hb : d168080 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137086, d168080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35492 q ha hb
    | true =>
      simp only [d137086, d168080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d137087 q = 1) (hb : d168081 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137087, d168081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d137087, d168081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d167259 q = 1) (hb : d168082 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167259, d168082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d167259, d168082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d167260 q = 1) (hb : d168083 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167260, d168083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d167260, d168083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d167261 q = 1) (hb : d168084 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167261, d168084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167261, d168084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d167262 q = 1) (hb : d168085 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167262, d168085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d167262, d168085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro35495 (p : Pattern) (ha : d167269 p = 1) (hb : d168094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d167257 q = 1) (hb : d168077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d167257, d168077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35493 q ha hb
    | true =>
      simp only [d167257, d168077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35466 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d136974 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d167258 q = 1) (hb : d168078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d167258, d168078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d167258, d168078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d137086 q = 1) (hb : d168080 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d137086, d168080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35492 q ha hb
    | true =>
      simp only [d137086, d168080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137087 q = 1) (hb : d168081 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d137087, d168081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137087, d168081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d167259 q = 1) (hb : d168082 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d167259, d168082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d167259, d168082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d167267 q = 1) (hb : d168092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d167267, d168092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167267, d168092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167268 q = 1) (hb : d168093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d167268, d168093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167268, d168093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167269 q = 1) (hb : d168094 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d167269, d168094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167269, d168094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro35496 (p : Pattern) (ha : d137124 p = 1) (hb : d168118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d136999 q = 1) (hb : d167991 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d136999, d167991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35470 q ha hb
    | true =>
      simp only [d136999, d167991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d137000 q = 1) (hb : d167992 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d137000, d167992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137000, d167992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d137121 q = 1) (hb : d168115 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d137121, d168115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d137121, d168115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d137122 q = 1) (hb : d168116 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d137122, d168116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d137122, d168116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d137123 q = 1) (hb : d168117 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d137123, d168117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d137123, d168117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d137124 q = 1) (hb : d168118 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d137124, d168118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d137124, d168118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro35497 (p : Pattern) (ha : d52182 p = 1) (hb : d168100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12858 q = 1) (hb : d52178 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12858, d52178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35484 q ha hb
  have h3 (q : Pattern) (ha : d9468 q = 1) (hb : d52118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35484 q ha hb
    | true =>
      simp only [d9468, d52118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12859 q = 1) (hb : d52179 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12859, d52179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9470 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9470, d52119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12860 q = 1) (hb : d52180 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12860, d52180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12861 q = 1) (hb : d52181 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12861, d52181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52047 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14371 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14371, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14371, d52182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52182 q = 1) (hb : d168100 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d168100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d168100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35498 (p : Pattern) (ha : d113011 p = 1) (hb : d167984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h3 (q : Pattern) (ha : d9382 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
    | true =>
      simp only [d9382, d101015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d12600 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12600, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9384 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9384, d101017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d12601 q = 1) (hb : d113009 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12601, d113009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12602 q = 1) (hb : d113010 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12602, d113010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d14155 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14155, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d14155, d113011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113011 q = 1) (hb : d167984 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d167984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro35499 (p : Pattern) (ha : d167279 p = 1) (hb : d168106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52182 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52182 q = 1) (hb : d168101 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35497 q ha hb
    | true =>
      simp only [d168101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d137108 q = 1) (hb : d168102 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d137108, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137108, d168102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d137109 q = 1) (hb : d168103 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d137109, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d137109, d168103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113011 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113011 q = 1) (hb : d167985 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d167985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35498 q ha hb
    | true =>
      simp only [d167985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d167275 q = 1) (hb : d167986 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d167275, d167986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167275, d167986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d167276 q = 1) (hb : d167987 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d167276, d167987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d167276, d167987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d167277 q = 1) (hb : d168104 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d167277, d168104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d167277, d168104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52048 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52048 q = 1) (hb : d167985 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d167985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35469 q ha hb
    | true =>
      simp only [d167985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d136994 q = 1) (hb : d167986 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d136994, d167986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136994, d167986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d136995 q = 1) (hb : d167987 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d136995, d167987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d136995, d167987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d51922 q = 1) (hb : d120103 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro35449 q ha hb
    | true =>
      simp only [d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d120104 q = 1) (hb : d136892 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d120104, d136892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120104, d136892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d120105 q = 1) (hb : d136893 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d120105, d136893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120105, d136893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d136996 q = 1) (hb : d167988 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d136996, d167988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d136996, d167988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d167278 q = 1) (hb : d168105 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d167278, d168105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d167278, d168105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d167279 q = 1) (hb : d168106 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d167279, d168106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d167279, d168106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
end NetHack.Soko22Hazard87
